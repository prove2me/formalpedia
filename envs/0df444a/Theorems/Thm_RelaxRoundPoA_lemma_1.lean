-- Prove2me | Theorems.Thm_RelaxRoundPoA_lemma_1
-- name    : RelaxRoundPoA.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:57.981479+00:00
-- url     : https://prove2.me/theorems/8184b3ea-0160-4bbd-9958-08a58f0e1b0c
-- title:
--   Lemma 1, p.8 — smooth and exact gives $(\lambda/2,\mu)$-smooth for half-value deviations
-- statement:
--   Let $M=(f,p)$ be a pay-your-bid mechanism with feasible outcomes $F$ that is $(\lambda,\mu)$-smooth, where $f$ is an exact declared welfare maximizer over $F$; expectations are finite and the weight classes are closed under halving. Then $M$ is $(\lambda/2,\mu)$-smooth for deviations to half the value: for all valuation and bid profiles $v,b$ drawn from the classes, with $b_i'=\tfrac12v_i$,
--
--   $$
--   \sum_{i\in N}u_i\bigl((b_i',b_{-i}),v_i\bigr)\ \ge\ \frac\lambda2\,\mathrm{OPT}(v)-\mu\sum_{i\in N}p_i(b).
--   $$
--
--   The deviations in the smoothness hypothesis are arbitrary and randomized; the lemma replaces them by one fixed deviation at the cost of a factor $2$, using exactness of $f$.
--
--   Differences from the source:
--   - generalization: weight functions w: Ω → ℝ≥0 generalized to Ω′, rounding guarantee "for all w" (p.6) → each agent's bids and valuations come from an arbitrary class Val i of functions Ω′ → ℝ≥0, read on Ω by restriction; reason: over every function the rounding guarantee is unsatisfiable when Ω ≠ Ω′; every weight class of §§4–7 is an instance, and a single common class is the case of equal Val i
--   - generalization: the proofs write the outcome rule as deterministic, f(b) a point → the outcome law is any probability measure on the outcome space, almost surely an exact declared welfare maximizer where exactness is assumed; reason: p.6 allows randomized outcomes and payments; a deterministic rule is the Dirac case (verification file, check (v))
--   - encoding: expectations E[v_i(f(b))], E[p_i(b)] taken to exist → ExpFinite: every member of Val i is integrable under every outcome law on profiles; reason: excludes only the cases in which the paper's expectations are undefined; a Bochner integral of a non-integrable function would be 0
--   - reading: bids ½v_i and pretended valuations ½v_i used without comment → hypothesis HalfClosed Val: w ∈ Val i implies ½w ∈ Val i; reason: the proof bids ½v_i, so it must be an admissible bid; every class of the applications is closed under halving
--   - encoding: λ · max_{x∈Ω} Σ_i v_i(x), i.e. λ OPT(v) → the inequality holds for every feasible outcome x; reason: equivalent when the maximum exists; avoids a real supremum, which is 0 on an unbounded set
--   - encoding: a possibly randomized deviation strategy b′_i (p.7) → a random variable into Val i on an arbitrary probability space (RandomBid), whose expected utility is integrable; reason: Mathlib has no σ-algebra on a class of functions; every mixture of bids arises this way
--   - generalization: the mechanism's outcome space Ω (p.8) → an arbitrary set Feas ⊆ Ω′ of feasible outcomes; reason: Feas = Set.univ is the relaxation M′ of Theorem 3, and the outcome space of any mechanism is a case of it
--   - encoding: agents N = {1, …, n} → any finite type N with decidable equality; reason: relabeling; at N = ∅ every sum is 0 and the statement stays true
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, Lemma 1, p.8

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_HalfClosed
import Definitions.Def_RelaxRoundPoA_IsPayYourBid
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsExactMaximizer
import Definitions.Def_RelaxRoundPoA_IsSmooth
import Definitions.Def_RelaxRoundPoA_IsSmoothHalf

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **Lemma 1.**
Dütting, Kesselheim, Tardos, *Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round*,
arXiv:1511.09208v1, Lemma 1, p.8: "Given a pay-your-bid mechanism `M = (f, p)` that is (λ, µ)-smooth where `f`
is an exact declared welfare maximizer. Then `M` is (λ/2, µ)-smooth for deviations to half the
value. That is, for all bid vectors `b` and bids `b'_i = ½ v_i` for all `i ∈ N`,
`∑_{i∈N} u_i((b'_i, b_{−i}), v_i) ≥ (λ/2) OPT(v) − µ ∑_{i∈N} p_i(b)`."

**Formalization Note** The smoothness hypothesis allows arbitrary randomized deviations
(`RandomBid`); the outcome rule is randomized (a deterministic rule is the Dirac case); `Feas` is
the outcome set over which `f` maximizes and `OPT` is taken. `HalfClosed Val` makes `½ v_i` an
admissible bid and valuation; `ExpFinite` makes the expectations finite. -/
theorem lemma_1 {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Feas : Set Ω') (M : Mechanism N Ω') (lam mu : ℝ) (hhalf : HalfClosed Val)
    (hpay : IsPayYourBid Val M) (hfin : ExpFinite Val M) (hexact : IsExactMaximizer Val Feas M)
    (hsmooth : IsSmooth Val Feas M lam mu) :
    IsSmoothHalf Val Feas M (lam / 2) mu := by sorry

end RelaxRoundPoA
