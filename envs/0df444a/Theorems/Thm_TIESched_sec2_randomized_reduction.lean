-- Prove2me | Theorems.Thm_TIESched_sec2_randomized_reduction
-- name    : TIESched.sec2_randomized_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:12.199259+00:00
-- url     : https://prove2.me/theorems/f2d13982-f5eb-4a80-b17a-67bc855efca7
-- title:
--   §2 — TIE randomized families induce truthful fractional families with the same guarantee
-- statement:
--   For a randomized mechanism family, the induced fractional mechanism $x_{ij}(p)=\mathbb E[X_{ij}(p)]$, $\pi_i(p)=\mathbb E[\Pi_i(p)]$
--
--   1. is feasible;
--   2. preserves expected utility under every report: for every nonnegative true row $p_i$ and nonnegative report $(\hat p_i,p_{-i})$,
--   $$\pi_i(\hat p_i,p_{-i})-p_i\cdot x_i(\hat p_i,p_{-i})=\mathbb E\big[\Pi_i(\hat p_i,p_{-i})-p_i\cdot X_i(\hat p_i,p_{-i})\big];$$
--   3. is truthful whenever the randomized family is truthful in expectation;
--   4. is $\Gamma$-approximate whenever the randomized family has a $\Gamma$-approximation guarantee in expectation, measured against $\mathrm{OPT}(p)$.
--
--   This transfers the fractional lower bound to TIE randomized mechanisms.
--
--   Differences from the source:
--   - generalization: a randomized family with internal randomness (random X(p), Π(p)) → one probability law of (integral allocation, payments) per job set and report; reason: every family with common internal randomness pushes forward to such a family with the same expected utilities and expected makespan, so the Lean statement specializes to the source's
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), §2, From randomized mechanisms to fractional mechanisms, p.8

import Mathlib
import Definitions.Def_TIESched_RandMech

set_option autoImplicit false

namespace TIESched

/-- **From randomized mechanisms to fractional mechanisms** (Wang, Xu, Zhang, arXiv:2611.05142, §2,
unnumbered, p.8). For a randomized mechanism family, the induced fractional mechanism
`x_ij(p) = E[X_ij(p)]`, `π_i(p) = E[Π_i(p)]` is feasible; it preserves the randomized mechanism's
expected utility under every report (for every true row `p_i`, deviation `p̂_i` and report `p_{-i}`,
`π_i(p̂_i, p_{-i}) − p_i · x_i(p̂_i, p_{-i}) = E[Π_i(p̂_i, p_{-i}) − p_i · X_i(p̂_i, p_{-i})]`); TIE
implies its truthfulness; and a Γ-approximation guarantee in expectation, measured against
`OPT(p)`, gives the same Γ-approximation guarantee for the induced fractional mechanism.

**Formalization Note.** The utility identity is stated for every nonnegative reported matrix `p'`
(any `(p̂_i, p_{-i})`) and every nonnegative true row `c`. -/
theorem sec2_randomized_reduction (m : ℕ) [NeZero m] (hm : 2 ≤ m) (R : RandMech m)
    (hR : IsRandMech R) :
    Feasible (inducedFrac R).alloc ∧
      (∀ (S : Finset ℕ) (p' : Fin m → S → ℝ) (i : Fin m) (c : S → ℝ), IsNonneg p' →
        (∀ j, 0 ≤ c j) →
        (inducedFrac R).pay S p' i - ∑ j, c j * (inducedFrac R).alloc S p' i j =
          expUtil R S p' i c) ∧
      (TruthfulInExpectation R → Truthful (inducedFrac R)) ∧
      ∀ Γ : ℝ, IsApproxInExpectation R Γ → IsApprox (inducedFrac R) Γ := by sorry

end TIESched
