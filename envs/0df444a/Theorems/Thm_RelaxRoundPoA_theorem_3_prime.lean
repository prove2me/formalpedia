-- Prove2me | Theorems.Thm_RelaxRoundPoA_theorem_3_prime
-- name    : RelaxRoundPoA.theorem_3_prime
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:52.687572+00:00
-- url     : https://prove2.me/theorems/0394e17f-8961-4672-bc95-c512d851dd17
-- title:
--   Theorem 3′, p.9 — half-value smooth relaxation gives a $(\lambda/\alpha,\mu)$-smooth rounded mechanism
-- statement:
--   Let $\Omega\subseteq\Omega'$ be the original and relaxed outcome spaces and let the weight classes be closed under halving. Let $M'=(f',p')$ be a pay-your-bid mechanism that solves the relaxation optimally (an exact declared welfare maximizer over $\Omega'$) and is $(\lambda,\mu)$-smooth for deviations to $b_i'=\tfrac12v_i$ over $\Omega'$. Let $M=(f,p)$ be a pay-your-bid mechanism for the original problem obtained from the relaxation through an $\alpha$-approximate oblivious rounding scheme, and let both have finite expectations. Then $M$ is $(\lambda/\alpha,\mu)$-smooth for deviations to half the value over $\Omega$: for all valuation and bid profiles $v,b$,
--
--   $$
--   \sum_{i\in N}\mathbf E\bigl[u_i((b_i',b_{-i}),v_i)\bigr]\ \ge\ \frac\lambda\alpha\max_{x\in\Omega}\sum_{i\in N}v_i(x)-\mu\sum_{i\in N}\mathbf E\bigl[p_i(b)\bigr].
--   $$
--
--   This is the paper's "stronger version" of its main theorem, used directly in its applications, where smoothness of the relaxation is proved through the half-value deviation.
--
--   **Formalization Note** The hypothesis that $M'$ solves the relaxation optimally is kept as printed although the paper's proof does not use it.
--
--   Differences from the source:
--   - generalization: weight functions w: Ω → ℝ≥0 generalized to Ω′, rounding guarantee "for all w" (p.6) → each agent's bids and valuations come from an arbitrary class Val i of functions Ω′ → ℝ≥0, read on Ω by restriction; reason: over every function the rounding guarantee is unsatisfiable when Ω ≠ Ω′; every weight class of §§4–7 is an instance, and a single common class is the case of equal Val i
--   - generalization: the proofs write the outcome rule as deterministic, f(b) a point → the outcome law is any probability measure on the outcome space, almost surely an exact declared welfare maximizer where exactness is assumed; reason: p.6 allows randomized outcomes and payments; a deterministic rule is the Dirac case (verification file, check (v))
--   - encoding: expectations E[v_i(f(b))], E[p_i(b)] taken to exist → ExpFinite: every member of Val i is integrable under every outcome law on profiles; reason: excludes only the cases in which the paper's expectations are undefined; a Bochner integral of a non-integrable function would be 0
--   - reading: bids ½v_i and pretended valuations ½v_i used without comment → hypothesis HalfClosed Val: w ∈ Val i implies ½w ∈ Val i; reason: the proof bids ½v_i, so it must be an admissible bid; every class of the applications is closed under halving
--   - encoding: λ · max_{x∈Ω} Σ_i v_i(x), i.e. λ OPT(v) → the inequality holds for every feasible outcome x; reason: equivalent when the maximum exists; avoids a real supremum, which is 0 on an unbounded set
--   - reading: for all w, E[w(x)] ≥ (1/α) w(x′) (p.6) → for every x′, every agent i and every w ∈ Val i: w(x′) ≤ α · E[w(x)], the expectation a lintegral; reason: p.3 says each agent is guaranteed a 1/α-fraction, and the proof of Theorem 3′ (p.9) applies the guarantee to one agent at a time; with 0 ∈ Val j for all j the total-weight form implies this one (verification file, check (iii))
--   - encoding: problem Π with outcomes Ω ⊆ Ω′; a randomized rounding scheme maps x′ to x → Ω is a set in the measurable space Ω′; the rounding is a Markov kernel R with R x′-almost every x in Ω; M's outcome law is the outcome law of M′ bound with R; reason: standard measure-theoretic form of a randomized map; measurability of the kernel is the field's standing convention
--   - generalization: conclusion: M is (λ/α, µ)-smooth → conclusion: M is (λ/α, µ)-smooth for deviations to half the value (IsSmoothHalf); reason: this implies the printed conclusion by isSmooth_of_half under HalfClosed Val, and it is the form the proof of Theorem 3 (p.9) uses
--   - encoding: agents N = {1, …, n} → any finite type N with decidable equality; reason: relabeling; at N = ∅ every sum is 0 and the statement stays true
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, Theorem 3′, p.9

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_HalfClosed
import Definitions.Def_RelaxRoundPoA_IsPayYourBid
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsExactMaximizer
import Definitions.Def_RelaxRoundPoA_IsObliviousRounding
import Definitions.Def_RelaxRoundPoA_IsRounded
import Definitions.Def_RelaxRoundPoA_IsSmoothHalf

open MeasureTheory ProbabilityTheory NNReal

namespace RelaxRoundPoA

/-- **Theorem 3′ (Stronger Version of Main Theorem).**
Dütting, Kesselheim, Tardos, *Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round*,
arXiv:1511.09208v1, Theorem 3′, p.9: "If the pay-your-bid mechanism `M' = (f', p')` that solves the relaxation
`Π'` optimally is (λ, µ)-smooth for deviations to `b'_i = ½ v_i`, then the pay-your-bid mechanism
`M = (f, p)` for `Π` that is obtained from the relaxation through an α-approximate oblivious
rounding scheme is (λ/α, µ)-smooth."

The relaxed outcome space is `Ω'` and the original outcomes form `Ω ⊆ Ω'`. `M'` is smooth for
half-value deviations over all of `Ω'`; the conclusion is that `M` is (λ/α, µ)-smooth for
half-value deviations over `Ω`, which gives the printed "(λ/α, µ)-smooth" by `isSmooth_of_half`.

**Formalization Note** The hypothesis `IsExactMaximizer Val Set.univ M'` ("solves the relaxation
optimally") is kept as printed although the paper's proof does not use it. The outcome rules are
randomized (a deterministic `f'` is the Dirac case); `ExpFinite` makes the expectations finite;
`HalfClosed Val` makes `½ v_i` an admissible bid. -/
theorem theorem_3_prime {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Ω : Set Ω') (α : ℝ) (R : Kernel Ω' Ω') (M' M : Mechanism N Ω') (lam mu : ℝ)
    (hhalf : HalfClosed Val) (hpay' : IsPayYourBid Val M') (hpay : IsPayYourBid Val M)
    (hfin' : ExpFinite Val M') (hfin : ExpFinite Val M)
    (hexact' : IsExactMaximizer Val Set.univ M') (hround : IsObliviousRounding Val Ω α R)
    (hrel : IsRounded Val M' R M) (hsmooth' : IsSmoothHalf Val Set.univ M' lam mu) :
    IsSmoothHalf Val Ω M (lam / α) mu := by sorry

end RelaxRoundPoA
