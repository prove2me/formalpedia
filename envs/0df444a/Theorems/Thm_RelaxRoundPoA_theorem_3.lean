-- Prove2me | Theorems.Thm_RelaxRoundPoA_theorem_3
-- name    : RelaxRoundPoA.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:15.647377+00:00
-- url     : https://prove2.me/theorems/e382e514-9225-4fae-bdde-b67cab2bb81e
-- title:
--   Theorem 3 (Main Result), p.8 — oblivious rounding of a smooth exact relaxation is $(\lambda/(2\alpha),\mu)$-smooth
-- statement:
--   Consider a problem with outcome set $\Omega$ and a relaxation with outcome space $\Omega'\supseteq\Omega$. Each agent's bids and valuations are weight functions on $\Omega'$ from a class closed under halving. Let $M'=(f',p')$ be a pay-your-bid mechanism for the relaxation that is $(\lambda,\mu)$-smooth (with arbitrary randomized deviations), where $f'$ is an exact declared welfare maximizer over $\Omega'$. Let $M=(f,p)$ be a pay-your-bid mechanism for the original problem obtained from the relaxation through an $\alpha$-approximate oblivious rounding scheme: $f$ computes $f'$ and rounds the result, and each bidder is charged its declared value of the rounded outcome. Assume all expectations are finite. Then $M$ is
--
--   $$
--   \Bigl(\frac{\lambda}{2\alpha},\ \mu\Bigr)\text{-smooth}.
--   $$
--
--   Through the smoothness framework of Syrgkanis and Tardos (which also requires that agents may withdraw), a Price of Anarchy bound of $\beta$ established via smoothness of $M'$ thus becomes a bound of $2\alpha\beta$ for the rounded mechanism $M$: a relax-and-round $\alpha$-approximation algorithm, run with pay-your-bid payments, is also a mechanism with Price of Anarchy $O(\alpha\beta)$.
--
--   Differences from the source:
--   - generalization: weight functions w: Ω → ℝ≥0 generalized to Ω′, rounding guarantee "for all w" (p.6) → each agent's bids and valuations come from an arbitrary class Val i of functions Ω′ → ℝ≥0, read on Ω by restriction; reason: over every function the rounding guarantee is unsatisfiable when Ω ≠ Ω′; every weight class of §§4–7 is an instance, and a single common class is the case of equal Val i
--   - generalization: the proofs write the outcome rule as deterministic, f(b) a point → the outcome law is any probability measure on the outcome space, almost surely an exact declared welfare maximizer where exactness is assumed; reason: p.6 allows randomized outcomes and payments; a deterministic rule is the Dirac case (verification file, check (v))
--   - encoding: expectations E[v_i(f(b))], E[p_i(b)] taken to exist → ExpFinite: every member of Val i is integrable under every outcome law on profiles; reason: excludes only the cases in which the paper's expectations are undefined; a Bochner integral of a non-integrable function would be 0
--   - reading: bids ½v_i and pretended valuations ½v_i used without comment → hypothesis HalfClosed Val: w ∈ Val i implies ½w ∈ Val i; reason: the proof bids ½v_i, so it must be an admissible bid; every class of the applications is closed under halving
--   - encoding: λ · max_{x∈Ω} Σ_i v_i(x), i.e. λ OPT(v) → the inequality holds for every feasible outcome x; reason: equivalent when the maximum exists; avoids a real supremum, which is 0 on an unbounded set
--   - encoding: a possibly randomized deviation strategy b′_i (p.7) → a random variable into Val i on an arbitrary probability space (RandomBid), whose expected utility is integrable; reason: Mathlib has no σ-algebra on a class of functions; every mixture of bids arises this way
--   - reading: for all w, E[w(x)] ≥ (1/α) w(x′) (p.6) → for every x′, every agent i and every w ∈ Val i: w(x′) ≤ α · E[w(x)], the expectation a lintegral; reason: p.3 says each agent is guaranteed a 1/α-fraction, and the proof of Theorem 3′ (p.9) applies the guarantee to one agent at a time; with 0 ∈ Val j for all j the total-weight form implies this one (verification file, check (iii))
--   - encoding: problem Π with outcomes Ω ⊆ Ω′; a randomized rounding scheme maps x′ to x → Ω is a set in the measurable space Ω′; the rounding is a Markov kernel R with R x′-almost every x in Ω; M's outcome law is the outcome law of M′ bound with R; reason: standard measure-theoretic form of a randomized map; measurability of the kernel is the field's standing convention
--   - encoding: agents N = {1, …, n} → any finite type N with decidable equality; reason: relabeling; at N = ∅ every sum is 0 and the statement stays true
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, Theorem 3, p.8

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_HalfClosed
import Definitions.Def_RelaxRoundPoA_IsPayYourBid
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsExactMaximizer
import Definitions.Def_RelaxRoundPoA_IsObliviousRounding
import Definitions.Def_RelaxRoundPoA_IsRounded
import Definitions.Def_RelaxRoundPoA_IsSmooth

open MeasureTheory ProbabilityTheory NNReal

namespace RelaxRoundPoA

/-- **Theorem 3 (Main Result).**
Dütting, Kesselheim, Tardos, *Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round*,
arXiv:1511.09208v1, Theorem 3, p.8: "Consider problem `Π` and a relaxation `Π'`. Given a pay-your-bid mechanism
`M' = (f', p')` that is (λ, µ)-smooth where `f'` is an exact declared welfare maximizer for the
relaxation `Π'`. Then a pay-your-bid mechanism `M = (f, p)` for the original problem `Π` that is
obtained from the relaxation through an α-approximate oblivious rounding scheme is
(λ/(2α), µ)-smooth."

The relaxed outcome space is the measurable space `Ω'` and the original outcomes form a set
`Ω ⊆ Ω'`. Agent `i`'s bids and valuations come from a class `Val i` of nonnegative weight functions
on `Ω'`, closed under halving. `M'` is pay-your-bid, an exact declared welfare maximizer over `Ω'`,
and (λ, µ)-smooth over `Ω'` with arbitrary randomized deviations. `M` is pay-your-bid and its outcome
is that of `M'` followed by an α-approximate oblivious rounding kernel `R`. Then `M` is
(λ/(2α), µ)-smooth over `Ω`.

**Formalization Note** `Val i` is an arbitrary per-agent class (the paper's "all `w`" over every
function would make every rounding impossible when `Ω ≠ Ω'`), and the rounding guarantee is per
agent (p.3). The outcome rules are randomized (a deterministic `f'` is the Dirac case);
randomized deviations are random variables into `Val i` (`RandomBid`); `max_{x∈Ω}` is read as
"for every `x ∈ Ω`"; `ExpFinite` makes every expectation finite. -/
theorem theorem_3 {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Ω : Set Ω') (α : ℝ) (R : Kernel Ω' Ω') (M' M : Mechanism N Ω') (lam mu : ℝ)
    (hhalf : HalfClosed Val) (hpay' : IsPayYourBid Val M') (hpay : IsPayYourBid Val M)
    (hfin' : ExpFinite Val M') (hfin : ExpFinite Val M)
    (hexact' : IsExactMaximizer Val Set.univ M') (hsmooth' : IsSmooth Val Set.univ M' lam mu)
    (hround : IsObliviousRounding Val Ω α R) (hrel : IsRounded Val M' R M) :
    IsSmooth Val Ω M (lam / (2 * α)) mu := by sorry

end RelaxRoundPoA
