-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary45_isomorphism
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.corollary45_isomorphism
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:52:36.933707+00:00
-- url     : https://prove2.me/theorems/bb717cfd-5399-425b-8e71-70e9c645633e
-- title:
--   Corollary 45: linear isomorphism onto the Choi spectral subspace
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   The rectangular transform $M$ identifies coefficient vectors with its Choi spectral subspace $\mathcal E=\operatorname{range}M$. Distinct sector coordinates may have equal numerical values. The inverse on this range is the Gram left inverse:
--
--   $$
--   \mathbb C^\Theta\xrightarrow[\cong]{\ L\mapsto ML\ }\mathcal E,\qquad\dim_{\mathbb C}\mathcal E=|\Theta|,\qquad M_{\mathrm{inv}}ML=L,\quad MM_{\mathrm{inv}}e=e\ (e\in\mathcal E).
--   $$
--
--   This describes the linear isomorphism onto the Choi spectral subspace in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 20, Corollary 45: linear isomorphism onto the Choi spectral subspace

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

/-- PDF p.20, Corollary 45 Eq.(101). No inequality between coefficient values is imposed. -/
theorem corollary45_isomorphism (D : Data G A n) (P : Pivots D) :
    Function.Injective (spectralMatrix D P).mulVec ∧
    Module.finrank ℂ (LinearMap.range (spectralMatrix D P).mulVecLin) = Fintype.card (OccurringIrrep D) ∧
    (∃ T : (OccurringIrrep D → ℂ) ≃ₗ[ℂ] LinearMap.range (spectralMatrix D P).mulVecLin,
      ∀ l, (T l).val = choiEigenvalueVector D P l) ∧
    (∀ l, (leftInverse D P).mulVec (choiEigenvalueVector D P l) = l) ∧
    ∀ e ∈ LinearMap.range (spectralMatrix D P).mulVecLin,
      choiEigenvalueVector D P ((leftInverse D P).mulVec e) = e := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
