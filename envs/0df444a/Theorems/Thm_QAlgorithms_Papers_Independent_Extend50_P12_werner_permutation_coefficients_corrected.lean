-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P12_werner_permutation_coefficients_corrected
-- name    : QAlgorithms.Papers.Independent.Extend50.P12.werner_permutation_coefficients_corrected
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:54:22.713147+00:00
-- url     : https://prove2.me/theorems/13f59785-fa06-4289-b800-3667b2682aa3
-- title:
--   Appendix B: conversion from the R basis to permutation coefficients, Eq.(B5)
-- statement:
--   Let $d\ge1$ and let $c_+,c_-,c_0,c_1,c_2,c_3$ be real. Using the six explicitly defined operators $R_+,R_-,R_0,R_1,R_2,R_3$ in Eq. (27), construct $\rho=\sum_j c_jR_j$, and assume that $\rho$ is PSD with trace one. Then
--   $$
--   \rho=\alpha_1I+\alpha_2V(12)+\alpha_3V(23)+\alpha_4V(31)+\alpha_5V(123)+\alpha_6V(321),
--   $$
--   where the physical permutation action is the one in Eq. (2), and
--   $$
--   \begin{aligned}
--   \alpha_1&=c_+/6+c_-/6+2c_0/3,&
--   \alpha_2&=c_+/6-c_-/6-c_1/3+c_2/\sqrt3,\\
--   \alpha_3&=c_+/6-c_-/6+2c_1/3,&
--   \alpha_4&=c_+/6-c_-/6-c_1/3-c_2/\sqrt3,\\
--   \alpha_5&=c_+/6+c_-/6-c_0/3+i c_3/\sqrt3,&
--   \alpha_6&=c_+/6+c_-/6-c_0/3-i c_3/\sqrt3.
--   \end{aligned}
--   $$
--   Here $i$ is the imaginary unit. This identity converts the two specified expansions of the same constructed Werner density matrix. It does not assert uniqueness of permutation coefficients at small $d$.
--
--   **Formalization Note** The displayed $\alpha_2$ corrects the printed Eq. (B5), which omits $-c_1/3$ and has the wrong sign on $c_2/\sqrt3$. Both changes are forced directly by the defining $R_1,R_2$ in Eq. (27), and require independent moderation.
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, PDF p. 13, Appendix B, Eqs.(B3)-(B5); corrected alpha_2 from Eq.(27)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-- Appendix B, PDF p.13, Eqs.(B3)-(B5), using the R definitions on p.5, Eq.(27).
SOURCE CORRECTION: the printed alpha_2=c_+/6-c_minus/6-c_2/sqrt(3) omits
-c_1/3 and has the wrong c_2 sign. Expanding Eq.(27) uniquely gives
alpha_2=c_+/6-c_minus/6-c_1/3+c_2/sqrt(3). The density is constructed from the
six real coefficients and is assumed PSD and trace one as in the section.
This is an equality of physical matrices, not an injectivity claim at small d. -/
theorem werner_permutation_coefficients_corrected
    (d : ℕ) (hd : 0 < d) (c : Fin 6 → ℝ)
    (hpositive : (wernerFromCoefficients d c).PosSemidef)
    (htrace : Matrix.trace (wernerFromCoefficients d c) = 1) :
    wernerFromCoefficients d c =
      ∑ j : Fin 6, correctedPermutationCoefficients c j • wernerPermutations d j := by sorry

end QAlgorithms.Papers.Independent.Extend50.P12

end
