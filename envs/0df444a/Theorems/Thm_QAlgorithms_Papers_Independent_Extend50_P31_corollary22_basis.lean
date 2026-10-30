-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary22_basis
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.corollary22_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:39:34.800982+00:00
-- url     : https://prove2.me/theorems/4e937a77-f88e-4af9-b357-72775becca36
-- title:
--   Corollary 22 with Remark 23: selected eigenmatrix basis
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Choose exactly one positive pivot for each fine sector $(\beta,i)$ and let $V_i^\beta$ be the resulting normalized matrices. They form a complete orthonormal basis of $M_n(\mathbb C)$:
--
--   $$
--   \sum_{\beta\in\Theta}d_\beta=n^2,\qquad (V_i^\beta,V_j^\gamma)=\delta_{\beta\gamma}\delta_{ij},\qquad\operatorname{span}_{\mathbb C}\{V_i^\beta\}=M_n(\mathbb C).
--   $$
--
--   This describes the selected eigenmatrix basis in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 13, Corollary 22 with Remark 23: selected eigenmatrix basis

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

/-- PDF pp.13--14, Corollary 22 and Remark 23: exactly ONE pivot per fine sector. -/
theorem corollary22_basis (D : Data G A n) (P : Pivots D) :
    Fintype.card (Row D) = n^2 ∧
    (∀ r s, hs (eigenmatrix D P r) (eigenmatrix D P s) = if r = s then 1 else 0) ∧
    Submodule.span ℂ (Set.range (eigenmatrix D P)) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
