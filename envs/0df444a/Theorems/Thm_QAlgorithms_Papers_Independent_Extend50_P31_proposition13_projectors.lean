-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition13_projectors
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.proposition13_projectors
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:32:41.367781+00:00
-- url     : https://prove2.me/theorems/e4c478b6-b5cb-42a7-993c-7a0ee490c814
-- title:
--   Proposition 13: character projectors form the commutant basis
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Define $\widetilde P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})U(g)\otimes\overline{U(g)}$. Their span is the entire commutant, of dimension $|\Theta|$. They form a complete orthogonal family of self-adjoint projectors:
--
--   $$
--   \widetilde P_\alpha\widetilde P_\beta=\delta_{\alpha\beta}\widetilde P_\alpha,\quad\widetilde P_\alpha^\dagger=\widetilde P_\alpha,\quad\sum_{\alpha\in\Theta}\widetilde P_\alpha=I_{n^2},\quad\operatorname{Tr}\widetilde P_\alpha=\operatorname{rank}\widetilde P_\alpha=d_\alpha.
--   $$
--
--   This describes the character projectors form the commutant basis in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 11, Proposition 13: character projectors form the commutant basis

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

/-- PDF p.11, Proposition 13 Eqs.(48)--(50): projectors are the computed Eq.(49) averages. -/
theorem proposition13_projectors (D : Data G A n) :
    representationCommutant (tensorConjugate D.U) =
      Submodule.span ℂ (Set.range (fun a : OccurringIrrep D => centralMatrix D.U D.F a.val)) ∧
    Module.finrank ℂ (representationCommutant (tensorConjugate D.U)) = Fintype.card (OccurringIrrep D) ∧
    (∀ a b : OccurringIrrep D, centralMatrix D.U D.F a.val * centralMatrix D.U D.F b.val =
      if a = b then centralMatrix D.U D.F a.val else 0) ∧
    (∀ a : OccurringIrrep D, (centralMatrix D.U D.F a.val)ᴴ = centralMatrix D.U D.F a.val) ∧
    (∑ a : OccurringIrrep D, centralMatrix D.U D.F a.val) = 1 ∧
    (∀ a : OccurringIrrep D, Matrix.trace (centralMatrix D.U D.F a.val) = (D.F.dim a.val : ℂ) ∧
      Matrix.rank (centralMatrix D.U D.F a.val) = D.F.dim a.val) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
