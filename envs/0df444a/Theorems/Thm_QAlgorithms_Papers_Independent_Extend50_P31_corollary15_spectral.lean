-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary15_spectral
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.corollary15_spectral
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:34:29.276724+00:00
-- url     : https://prove2.me/theorems/70c81690-375a-4a95-b210-f5430a6be619
-- title:
--   Corollary 15 and Remark 16: spectral form of an ICLM
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Every complex-linear $U$-covariant map $\Phi$ has a spectral expansion in the computed character averages $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$. They are Hilbert–Schmidt self-adjoint and mutually orthogonal, sum to the identity map, and have matrix representatives $\widetilde P_\alpha$. Each range is nonzero, and the corresponding coefficient acts on the whole range as an eigenvalue:
--
--   $$
--   \Phi=\sum_{\alpha\in\Theta}l_\alpha P_\alpha,\quad l_\alpha\in\mathbb C,\qquad\Phi(P_\alpha X)=l_\alpha P_\alpha X.\quad P_\alpha P_\beta=\delta_{\alpha\beta}P_\alpha.
--   $$
--
--   Equal coefficient values in different sectors are allowed. This gives the spectral parametrization of the full covariant endomorphism algebra.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 11, Corollary 15 and Remark 16: spectral form of an ICLM

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

/-- PDF pp.11--12, Corollary 15 and Remark 16. Equal eigenvalues across sectors are allowed. -/
theorem corollary15_spectral (D : Data G A n) (Phi : EndMat n) (hPhi : IsIrrepCovariant D.U Phi) :
    (∃ l : OccurringIrrep D → ℂ, Phi = spectralMap D l ∧
      ∀ a : OccurringIrrep D,
        (∃ X : Mat n, X ≠ 0 ∧ centralMap D.U D.F a.val X = X) ∧
        ∀ X : Mat n, Phi (centralMap D.U D.F a.val X) = l a • centralMap D.U D.F a.val X) ∧
    (∀ a : OccurringIrrep D, rowMatrixRepresentative (centralMap D.U D.F a.val) = centralMatrix D.U D.F a.val) ∧
    (∀ a b : OccurringIrrep D, (centralMap D.U D.F a.val).comp (centralMap D.U D.F b.val) =
      if a = b then centralMap D.U D.F a.val else 0) ∧
    (∀ a : OccurringIrrep D, hsAdjoint (centralMap D.U D.F a.val) = centralMap D.U D.F a.val) ∧
    (∑ a : OccurringIrrep D, centralMap D.U D.F a.val) = LinearMap.id := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
