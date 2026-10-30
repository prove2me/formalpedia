-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P12_example6_threeToTwo
-- name    : QAlgorithms.Papers.Independent.Extend50.P12.example6_threeToTwo
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:51:22.510985+00:00
-- url     : https://prove2.me/theorems/fc97d7d0-934c-4d4c-b74c-9b980aa7acaf
-- title:
--   Example 6: 3-to-2 evaluation, Eq.(37)
-- statement:
--   Let $d\ge1$ and $X_1,X_2,X_3\in M_d(\mathbb C)$ be arbitrary complex matrices. Use the permutation action of Eq. (2), ordinary partial transpose $T_j$, the unnormalized partial trace, and the two-site reshuffling $R$ of Eq. (6). Then
--   $$
--   \operatorname{tr}_{123}\!\left[V(12345)^{T_2}(X_1\otimes X_2\otimes X_3\otimes I\otimes I)\right]
--   =\left[\left(X_3X_2^TX_1\otimes I\right)^R\right]^{T_2}.
--   $$
--   The right-hand side acts on the two output registers. No Hermiticity, positivity or trace restriction is imposed on the inputs.
--
--   This identity evaluates the specified three-input, two-output contraction using matrix multiplication, transpose and reshuffling.
--
--   **Formalization Note** A direct index audit shows that the printed matrix-unit kernel agrees with the forward cycle under Eq. (2). The plan's proposed inverse-cycle obstruction was incorrect; the source formula is retained unchanged.
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, PDF p. 6, Example 6, Eq.(37)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-- Example 6, PDF p.6, Eq.(37), with the fixed Eq.(2) cycle convention.
The printed kernel is that convention's forward five-cycle with site 2
transposed, as a direct coordinate substitution verifies. -/
theorem example6_threeToTwo (d : ℕ) (hd : 0 < d) (X1 X2 X3 : LocalMatrix d) :
    productInputContraction (r := 3) (m := 2)
      (transposeRegisterSet {1} (permutation d 5 (finRotate 5))) ![X1, X2, X3] =
    transposeRegisterSet {1}
      (reshuffleTwo (homogeneousTensorPair (X3 * X2.transpose * X1) 1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P12

end
