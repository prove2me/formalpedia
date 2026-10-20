-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P49_continuity_free_dilations
-- name    : QAlgorithms.Papers.Independent.Dependency50.P49.continuity_free_dilations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:17:37.955845+00:00
-- url     : https://prove2.me/theorems/8575b617-1337-49e9-ad2e-f563c915fc85
-- title:
--   Continuity with freely chosen common Stinespring dilations
-- statement:
--   Let $H_A$ and $H_B$ be positive-dimensional finite complex Hilbert spaces, and let $T_1,T_2:\mathcal B(H_B)\to\mathcal B(H_A)$ be completely positive unital complex-linear maps. Define $\beta(T_1,T_2)$ as the infimum of $\|V_1-V_2\|_\infty$ over all positive-dimensional finite common environments $H_E$ and all isometries $V_i:H_A\to H_B\otimes H_E$ satisfying $T_i(b)=V_i^*(b\otimes I_E)V_i$. Then
--
--   $$\beta(T_1,T_2)^2\leq\|T_1-T_2\|_{\rm cb}\leq 2\beta(T_1,T_2).$$
--
--   Here the isometry norm is the Hilbert-space operator norm and the cb-norm is the supremum of induced operator norms over all finite reference systems, without a factor of one half. The environment is part of the optimization. This is the continuity result used by the information–disturbance argument.
-- source:
--   The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation, arXiv:quant-ph/0605009v1, PDF p. 1, §I, Eq. (1)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker Topology ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Information100.P50 (coefficientMap)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

namespace QAlgorithms.Papers.Independent.Dependency50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- The accepted all-Schatten norms at p=top are exactly the source's operator norms.

local notation "inducedNorm" => QAlgorithms.Papers.Independent.Information100.P50.inducedNorm (⊤ : ℝ≥0∞)

local notation "cbNorm" => QAlgorithms.Papers.Independent.Information100.P50.cbNorm (⊤ : ℝ≥0∞)

/-- PDF p.1, (1), with pp.5–8: continuity for freely chosen common Stinespring
isometries. The environment is optimized. Squaring the nonnegative infimum equals
the printed infimum of squared distances. This does not assert the false (18). -/
theorem continuity_free_dilations {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (T1 T2 : MatrixMap (Fin b) (Fin a))
    (hT1 : IsQuantumChannel T1) (hT2 : IsQuantumChannel T2) :
    dilationDistance T1 T2 ^ 2 ≤ cbNorm (T1 - T2) ∧
      cbNorm (T1 - T2) ≤ 2 * dilationDistance T1 T2 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P49

end
