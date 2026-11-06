-- Prove2me | Theorems.Thm_TIESched_theorem_1_lower_bound
-- name    : TIESched.theorem_1_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:02.953922+00:00
-- url     : https://prove2.me/theorems/4d0e89d2-c71c-453a-a76c-9919bf950be2
-- title:
--   Theorem 1 — truthful fractional and TIE randomized scheduling mechanisms have ratio $\Gamma\ge(m+1)/2$
-- statement:
--   Consider makespan minimization on $m\ge2$ unrelated machines, each machine privately knowing its row of processing times, with mechanisms defined on all nonnegative reports (zero times allowed) for every finite job set. Let $\Gamma\in\mathbb R$.
--
--   1. Every feasible, truthful, $\Gamma$-approximate fractional mechanism family satisfies
--   $$\Gamma\ \ge\ \frac{m+1}{2}.$$
--   2. The same lower bound holds for truthful-in-expectation randomized mechanism families: if such a family has $\mathbb E[C(p,X(p))]\le\Gamma\,\mathrm{OPT}(p)$ for every nonempty instance with $\mathrm{OPT}(p)>0$, then $\Gamma\ge(m+1)/2$.
--
--   Here the benchmark $\mathrm{OPT}$ is the optimal integral makespan. The previous lower bound for truthful-in-expectation mechanisms was $2-1/m$.
--
--   **Formalization Note.** No measurability, continuity or positivity is assumed of the mechanisms.
--
--   Differences from the source:
--   - reading: a Γ-approximation guarantee in expectation → E[C(p, X(p))] ≤ Γ·OPT(p) for nonempty S and nonnegative p with OPT(p) > 0; reason: the scope of the Γ-approximation guarantee of p.8; the weakest hypothesis, so the strongest theorem
--   - generalization: a randomized family with internal randomness (random X(p), Π(p)) → one probability law of (integral allocation, payments) per job set and report; reason: every family with common internal randomness pushes forward to such a family with the same expected utilities and expected makespan, so the Lean statement specializes to the source's
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Theorem 1, p.11

import Mathlib
import Definitions.Def_TIESched_RandMech

set_option autoImplicit false

namespace TIESched

/-- **Theorem 1 (Our main result)** (Wang, Xu, Zhang, *Tight Analysis of Randomized Truthful
Scheduling: An (m+1)/2 Lower Bound*, arXiv:2611.05142, Theorem 1, p.11). For `m ≥ 2` unrelated
machines, every truthful, Γ-approximate fractional mechanism family satisfies `Γ ≥ (m + 1)/2`. The
same lower bound holds for truthful-in-expectation randomized mechanism families.

**Formalization Note.** Mechanisms are defined on all nonnegative reports (zero processing times
allowed) on every finite job set `S ⊆ ℕ`; the benchmark `OPT` is the optimal *integral* makespan;
Γ-approximation is required for nonempty `S` with `OPT(p) > 0` (p.8); `Γ` is any real number. No
measurability, continuity or positivity is assumed of the mechanisms. A randomized family is a law
of (integral allocation, payments) per report, with finite expected payments; its guarantee is
`E[C(p, X(p))] ≤ Γ · OPT(p)`. -/
theorem theorem_1_lower_bound (m : ℕ) [NeZero m] (hm : 2 ≤ m) (Γ : ℝ) :
    (∀ M : FracMech m, Feasible M.alloc → Truthful M → IsApprox M Γ →
        ((m : ℝ) + 1) / 2 ≤ Γ) ∧
      ∀ R : RandMech m, IsRandMech R → TruthfulInExpectation R → IsApproxInExpectation R Γ →
        ((m : ℝ) + 1) / 2 ≤ Γ := by sorry

end TIESched
