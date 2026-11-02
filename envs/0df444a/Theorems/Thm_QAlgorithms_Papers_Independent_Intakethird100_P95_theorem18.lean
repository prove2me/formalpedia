-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_theorem18
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.theorem18
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:36:19.353571+00:00
-- url     : https://prove2.me/theorems/2d8ef118-2a10-4152-a892-f717fa064067
-- title:
--   Theorem 18: exact rank-three preparation from an EPR pair
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. For a positive integer $K$, $\Phi_K$ denotes the maximally entangled state of Schmidt rank $K$. Assume that $\lambda$ has exactly three strictly positive entries, ordered as $\lambda_1^\uparrow\le\lambda_2^\uparrow\le\lambda_3^\uparrow$. Then
--
--   $$\Phi_2\to^{\rm PPT}\rho_\lambda\quad\Longleftrightarrow\quad2\bigl(\sqrt{\lambda_3^\uparrow\lambda_2^\uparrow}+\sqrt{\lambda_3^\uparrow\lambda_1^\uparrow}\bigr)+4\sqrt{\lambda_1^\uparrow\lambda_2^\uparrow}\le1.$$
--
--   This is the exact rank-three preparation criterion from one EPR pair.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 8, Theorem 18: exact rank-three preparation from an EPR pair

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

/-- PDF p.8, Theorem 18, (47): ordered Schmidt probabilities, coefficients 2,2,4. -/
theorem theorem18 (lam : Fin 3 → ℝ) (hprob : IsProbability lam)
    (hpos : ∀ i, 0 < lam i) (hsorted : Monotone lam) :
    Reach (maximallyEntangledDensity 2) (schmidtDensity lam) ↔
      2 * (Real.sqrt (lam 2 * lam 1) + Real.sqrt (lam 2 * lam 0)) +
        4 * Real.sqrt (lam 0 * lam 1) ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
