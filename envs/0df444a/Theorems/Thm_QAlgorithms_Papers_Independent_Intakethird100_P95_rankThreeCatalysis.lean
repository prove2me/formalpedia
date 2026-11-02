-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_rankThreeCatalysis
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.rankThreeCatalysis
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:39:30.426589+00:00
-- url     : https://prove2.me/theorems/ea2afd92-1b90-4863-b030-2a83cea968a7
-- title:
--   Equation (51) and Figure 1: rank-three catalytic region, strict boundary corrected
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. For a positive integer $K$, $\Phi_K$ denotes the maximally entangled state of Schmidt rank $K$. Assume the target has three strictly positive probabilities in nondecreasing order. Then
--
--   $$\bigl[\exists C\ge2:\;\Phi_C\otimes\Phi_2\to^{\rm PPT}\Phi_C\otimes\rho_\lambda\bigr]\quad\Longleftrightarrow\quad2\bigl(\sqrt{\lambda_3^\uparrow\lambda_2^\uparrow}+\sqrt{\lambda_3^\uparrow\lambda_1^\uparrow}+\sqrt{\lambda_1^\uparrow\lambda_2^\uparrow}\bigr)<1.$$
--
--   This gives the finite-catalyst preparation region of Figure 1.
--
--   **Source correction.** Equation (51) prints a non-strict inequality, but Theorem 21 requires the strict inequality displayed here.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 9, Equation (51) and Figure 1: rank-three catalytic region, strict boundary corrected

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P95

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P95

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from the pinned accepted library; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

/-- PDF p.9, (51), CORRECTED BOUNDARY: printed ≤1 is replaced by <1, as required
by Theorem 21. The positive spectrum (1/18,1/18,8/9) has S_{1/2}=1 and
cannot be prepared with any finite catalyst, so the printed equality case is false. -/
theorem rankThreeCatalysis (lam : Fin 3 → ℝ) (hprob : IsProbability lam)
    (hpos : ∀ i, 0 < lam i) (hsorted : Monotone lam) :
    CatalyticPreparation 2 lam ↔
      2 * (Real.sqrt (lam 2 * lam 1) + Real.sqrt (lam 2 * lam 0) +
        Real.sqrt (lam 0 * lam 1)) < 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
