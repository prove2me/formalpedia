-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary14_absent
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.corollary14_absent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:33:27.438807+00:00
-- url     : https://prove2.me/theorems/36f2eac8-509f-44c4-b3d6-868be3a095f4
-- title:
--   Corollary 14: trivial sector and zero absent sectors
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Use the same character-sum formula for every irreducible label, whether or not it occurs. Then
--
--   $$
--   \mathrm{id}\in\Theta,\qquad\gamma\notin\Theta\ \Longrightarrow\ \widetilde P_\gamma=0.
--   $$
--
--   This describes the trivial sector and zero absent sectors in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 11, Corollary 14: trivial sector and zero absent sectors

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

/-- PDF p.11, Corollary 14 Eq.(51), including all absent labels. -/
theorem corollary14_absent (D : Data G A n) :
    D.F.trivial ∈ D.theta ∧
    ∀ a : A, a ∉ D.theta → centralMatrix D.U D.F a = 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
