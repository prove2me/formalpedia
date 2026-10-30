-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary19_refinement
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.corollary19_refinement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:36:20.760626+00:00
-- url     : https://prove2.me/theorems/a6ab8814-9e91-4be2-86f6-a243d6df4ca9
-- title:
--   Corollary 19: rank-one superoperator refinement
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Define $P_{\alpha i}=(d_\alpha/|G|)\sum_g\varphi^\alpha(g^{-1})_{ii}\operatorname{Ad}_U(g)$. Their matrix representatives are $\widetilde P_{\alpha i}$, and
--
--   $$
--   P_\alpha=\sum_iP_{\alpha i},\qquad P_{\alpha i}P_{\beta j}=\delta_{\alpha\beta}\delta_{ij}P_{\alpha i},\qquad P_{\alpha i}^*=P_{\alpha i}.
--   $$
--
--   This describes the rank-one superoperator refinement in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 12, Corollary 19: rank-one superoperator refinement

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.12, Corollary 19 Eqs.(59),(60). -/
theorem corollary19_refinement (D : Data G A n) :
    (∀ r : Row D, rowMatrixRepresentative (fineMap D.U D.F r.1.val r.2) = fineMatrix D.U D.F r.1.val r.2) ∧
    (∀ a : OccurringIrrep D, centralMap D.U D.F a.val =
      ∑ i : Fin (D.F.dim a.val), fineMap D.U D.F a.val i) ∧
    (∀ r s : Row D, (fineMap D.U D.F r.1.val r.2).comp (fineMap D.U D.F s.1.val s.2) =
      if r = s then fineMap D.U D.F r.1.val r.2 else 0) ∧
    (∀ r : Row D, hsAdjoint (fineMap D.U D.F r.1.val r.2) = fineMap D.U D.F r.1.val r.2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
