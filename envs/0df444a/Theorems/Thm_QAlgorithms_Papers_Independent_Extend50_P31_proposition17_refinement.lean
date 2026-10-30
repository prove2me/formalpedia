-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition17_refinement
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.proposition17_refinement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:35:26.830733+00:00
-- url     : https://prove2.me/theorems/038b0181-ccf3-4c7d-b033-89aed14cb41a
-- title:
--   Proposition 17: rank-one matrix-unit projector refinement
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   In each fixed irrep coordinate basis define $\widetilde P_{\alpha i}=(d_\alpha/|G|)\sum_g\varphi^\alpha(g^{-1})_{ii}\,U(g)\otimes\overline{U(g)}$, for $1\le i\le d_\alpha$. Then
--
--   $$
--   \widetilde P_\alpha=\sum_i\widetilde P_{\alpha i},\quad\widetilde P_{\alpha i}\widetilde P_{\beta j}=\delta_{\alpha\beta}\delta_{ij}\widetilde P_{\alpha i},\quad\widetilde P_{\alpha i}^\dagger=\widetilde P_{\alpha i},\quad\operatorname{Tr}\widetilde P_{\alpha i}=\operatorname{rank}\widetilde P_{\alpha i}=1.
--   $$
--
--   This describes the rank-one matrix-unit projector refinement in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 12, Proposition 17: rank-one matrix-unit projector refinement

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

/-- PDF p.12, Proposition 17 Eqs.(56),(57). Trace/rank one are conclusions, not input fields. -/
theorem proposition17_refinement (D : Data G A n) :
    (∀ a : OccurringIrrep D, centralMatrix D.U D.F a.val =
      ∑ i : Fin (D.F.dim a.val), fineMatrix D.U D.F a.val i) ∧
    (∀ r s : Row D, fineMatrix D.U D.F r.1.val r.2 * fineMatrix D.U D.F s.1.val s.2 =
      if r = s then fineMatrix D.U D.F r.1.val r.2 else 0) ∧
    (∀ r : Row D, (fineMatrix D.U D.F r.1.val r.2)ᴴ = fineMatrix D.U D.F r.1.val r.2 ∧
      Matrix.trace (fineMatrix D.U D.F r.1.val r.2) = 1 ∧
      Matrix.rank (fineMatrix D.U D.F r.1.val r.2) = 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
