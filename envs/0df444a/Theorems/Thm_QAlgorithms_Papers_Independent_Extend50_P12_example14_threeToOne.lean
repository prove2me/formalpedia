-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P12_example14_threeToOne
-- name    : QAlgorithms.Papers.Independent.Extend50.P12.example14_threeToOne
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:53:17.398071+00:00
-- url     : https://prove2.me/theorems/1a7a14cc-a408-4862-ad2c-a8f7412ec4a2
-- title:
--   Example 14: three-input qubit positive map, Eq.(58)
-- statement:
--   For four qubit registers let $V(\pi)$ be the physical permutation action, and define the following operators, with identity on unused sites:
--   $$
--   P_\alpha=\frac{I+V(12)}2,\quad
--   P_\mu=\frac{2I-V(123)-V(132)}3,\quad
--   \sigma=V(34)^{T_4},
--   $$
--   $$
--   F=P_\mu\big[P_\alpha\sigma+V(23)P_\alpha\sigma V(23)+V(13)P_\alpha\sigma V(13)\big].
--   $$
--   For arbitrary complex $2\times2$ matrices $A,B,C$, the unnormalized partial-trace map has the exact evaluation
--   $$
--   \begin{aligned}
--   \operatorname{tr}_{123}[F(A\otimes B\otimes C\otimes I)]
--   ={}&-\frac16\big[(ACB)^T+(BAC)^T+(CBA)^T+(ABC)^T+(BCA)^T+(CAB)^T\big]\\
--   &+\frac13\big[\operatorname{tr}(B)\operatorname{tr}(C)A^T+
--   \operatorname{tr}(A)\operatorname{tr}(C)B^T+
--   \operatorname{tr}(A)\operatorname{tr}(B)C^T\big].
--   \end{aligned}
--   $$
--   Moreover, this matrix is PSD whenever $A,B,C$ are PSD. Transpose is ordinary transpose in the fixed basis; the input traces need not be one.
--
--   This is the three-input, one-output positive map for $N=4$, $k=1$, $d=2$, $\alpha=(2)$, $\mu=(2,1)$ and $\gamma=1$, with its kernel constructed by the first line of Eq. (56).
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, PDF p. 9, Example 14, Eqs.(55),(56),(58)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-- Example 14, PDF p.9, Eq.(58), with F constructed by the first line of
Eq.(56) and Eq.(55). The evaluation holds on arbitrary complex matrices;
positivity holds on all PSD matrices without trace-one restrictions.
Both orientations of each cycle occur with equal coefficients in F. -/
theorem example14_threeToOne :
    (∀ A B C : LocalMatrix 2, example14Map A B C = example14Formula A B C) ∧
    (∀ A B C : LocalMatrix 2, A.PosSemidef → B.PosSemidef → C.PosSemidef →
      (example14Map A B C).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P12

end
