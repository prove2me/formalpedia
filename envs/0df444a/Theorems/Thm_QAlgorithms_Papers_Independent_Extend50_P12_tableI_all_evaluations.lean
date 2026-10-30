-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P12_tableI_all_evaluations
-- name    : QAlgorithms.Papers.Independent.Extend50.P12.tableI_all_evaluations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:53:52.312307+00:00
-- url     : https://prove2.me/theorems/ca77bb61-0e62-4d14-9e58-b00d8b357cc8
-- title:
--   Example 3 and Appendix B Table I: all twelve explicit map evaluations
-- statement:
--   Let $d\ge1$ and $\alpha_1,\ldots,\alpha_6\in\mathbb C$. Construct the physical matrix
--   $$
--   \rho=\alpha_1I+\alpha_2V(12)+\alpha_3V(23)+\alpha_4V(31)+\alpha_5V(123)+\alpha_6V(321),
--   $$
--   and suppose that $\rho$ is PSD and has trace one. For each $S\in\{1,2,3,12,13,23\}$, define $f_S(A)=\operatorname{tr}_1[\rho^{T_S}(A\otimes I\otimes I)]$ and $g_S(A,B)=\operatorname{tr}_{12}[\rho^{T_S}(A\otimes B\otimes I)]$. The labels $12,13,23$ denote the corresponding two-element subsets. All traces are unnormalized; all transposes are ordinary basis transposes.
--
--   For arbitrary complex input matrices, all twelve evaluations in Table I hold exactly, with their six labelled permutation coefficients, product orders, partial transposes and reshufflings. In particular, writing $A'=A^T$, $B'=B^T$, $t=\operatorname{tr}(A)$, $u=\operatorname{tr}(B)$, and $R$ for the two-site reshuffling, the six $f$ evaluations are
--   $$
--   \begin{aligned}
--   f_1(A)&=\alpha_1t(I\otimes I)+\alpha_2(A'\otimes I)+\alpha_3t[(I\otimes I)^R]^{T_2}+\alpha_4(I\otimes A')+\alpha_5[(A'\otimes I)^R]^{T_2}+\alpha_6[(I\otimes A)^R]^{T_2},\\
--   f_2(A)&=\alpha_1t(I\otimes I)+\alpha_2(A'\otimes I)+\alpha_3t(I\otimes I)^R+\alpha_4(I\otimes A)+\alpha_5(I\otimes A)^R+\alpha_6(A'\otimes I)^R,\\
--   f_3(A)&=\alpha_1t(I\otimes I)+\alpha_2(A\otimes I)+\alpha_3t(I\otimes I)^R+\alpha_4(I\otimes A')+\alpha_5(A\otimes I)^R+\alpha_6(I\otimes A')^R,\\
--   f_{12}(A)&=\alpha_1t(I\otimes I)+\alpha_2(A\otimes I)+\alpha_3t(I\otimes I)^R+\alpha_4(I\otimes A')+\alpha_5(I\otimes A')^R+\alpha_6(A\otimes I)^R,\\
--   f_{13}(A)&=\alpha_1t(I\otimes I)+\alpha_2(A'\otimes I)+\alpha_3t(I\otimes I)^R+\alpha_4(I\otimes A)+\alpha_5(A'\otimes I)^R+\alpha_6(I\otimes A)^R,\\
--   f_{23}(A)&=\alpha_1t(I\otimes I)+\alpha_2(A'\otimes I)+\alpha_3t[(I\otimes I)^R]^{T_2}+\alpha_4(I\otimes A')+\alpha_5[(I\otimes A)^R]^{T_2}+\alpha_6[(A'\otimes I)^R]^{T_2}.
--   \end{aligned}
--   $$
--   The six $g$ evaluations, with $c=\alpha_1tuI$, are
--   $$
--   \begin{aligned}
--   g_1(A,B)&=c+\alpha_2\operatorname{tr}(A'B)I+\alpha_3tB+\alpha_4uA'+\alpha_5BA'+\alpha_6A'B,\\
--   g_2(A,B)&=c+\alpha_2\operatorname{tr}(AB')I+\alpha_3tB'+\alpha_4uA+\alpha_5B'A+\alpha_6AB',\\
--   g_3(A,B)&=c+\alpha_2\operatorname{tr}(AB)I+\alpha_3tB'+\alpha_4uA'+\alpha_5A'B'+\alpha_6B'A',\\
--   g_{12}(A,B)&=c+\alpha_2\operatorname{tr}(A'B')I+\alpha_3tB'+\alpha_4uA'+\alpha_5B'A'+\alpha_6A'B',\\
--   g_{13}(A,B)&=c+\alpha_2\operatorname{tr}(A'B)I+\alpha_3tB'+\alpha_4uA+\alpha_5AB'+\alpha_6B'A,\\
--   g_{23}(A,B)&=c+\alpha_2\operatorname{tr}(A'B)I+\alpha_3tB+\alpha_4uA'+\alpha_5A'B+\alpha_6BA'.
--   \end{aligned}
--   $$
--   Furthermore,
--   $$
--   f_3(A^T)=f_{13}(A),\quad f_2(A^T)=f_{12}(A),\quad
--   g_{13}(A^T,B^T)=g_{23}(A,B),\quad g_1(A^T,B^T)=g_2(A,B).
--   $$
--   These evaluations include Example 3 and retain the table's exact labelled coefficients. Its positivity caption is represented separately by Proposition 4. The plan's alleged cycle reversal does not occur: the $\alpha_5$ contribution to $g_3$ is $A^TB^T$ under Eq. (2).
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, PDF p. 13, Example 3, Eq.(31); Appendix B, Table I and relations below (B5)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-- Example 3 and all twelve Table I evaluations, PDF pp.5,13, plus the four
input-transpose relations below Eq.(B5). The coefficients define rho physically;
PSD and trace one are the section's state premise. Both orientations of the
labelled cycles use exactly Eq.(2); the table's alpha_5 contribution to g_3
is A^T B^T, as verified by the kernel |k i k><i j j|. -/
theorem tableI_all_evaluations (d : ℕ) (hd : 0 < d) (a : Fin 6 → ℂ)
    (hpositive : (permutationExpansion d a).PosSemidef)
    (htrace : Matrix.trace (permutationExpansion d a) = 1) :
    let rho := permutationExpansion d a
    (∀ s : Fin 6, ∀ A : LocalMatrix d,
      tripartiteF rho (tableSubsets s) A = tableF a A s) ∧
    (∀ s : Fin 6, ∀ A B : LocalMatrix d,
      tripartiteG rho (tableSubsets s) A B = tableG a A B s) ∧
    (∀ A : LocalMatrix d,
      tripartiteF rho {2} A.transpose = tripartiteF rho {0, 2} A ∧
      tripartiteF rho {1} A.transpose = tripartiteF rho {0, 1} A) ∧
    (∀ A B : LocalMatrix d,
      tripartiteG rho {0, 2} A.transpose B.transpose = tripartiteG rho {1, 2} A B ∧
      tripartiteG rho {0} A.transpose B.transpose = tripartiteG rho {1} A B) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P12

end
