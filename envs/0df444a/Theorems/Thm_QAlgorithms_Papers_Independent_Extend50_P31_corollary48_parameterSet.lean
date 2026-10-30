-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary48_parameterSet
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.corollary48_parameterSet
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:54:12.503768+00:00
-- url     : https://prove2.me/theorems/7865cb4b-ab30-416a-b6c7-ba0344034a05
-- title:
--   Corollary 48 and Remark 49: exact channel parameter set
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   For arbitrary complex sector coefficients $L=(l_\alpha)$ and $\Phi_l=\sum l_\alpha P_\alpha$, the exact channel parameter set is the inverse image of the scaled simplex section. The total eigenvalue sum also detects trace preservation:
--
--   $$
--   \Phi_l\text{ is a channel}\ \Longleftrightarrow\ \exists e\in\Sigma_n\cap\operatorname{range}M:\ L=M_{\mathrm{inv}}e,\qquad\sum_{\beta,i}\epsilon_i^\beta=n\ \Longleftrightarrow\ l_{\mathrm{id}}=1\ \Longleftrightarrow\Phi_l\text{ is TP}.
--   $$
--
--   This describes the exact channel parameter set in the fixed source conventions.
--
--   **Formalization Note** The trivial coefficient is extracted by summing the coefficient at the trivial label, without assuming in the input data the theorem that this label occurs.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 20, Corollary 48 and Remark 49: exact channel parameter set

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

/-- PDF p.20, Corollary 48 and Remark 49. Off-range nonnegative vectors are excluded. -/
theorem corollary48_parameterSet (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ) :
    (IsPaperChannel (spectralMap D l) ↔ ∃ e : Row D → ℂ,
      e ∈ scaledSimplex D ∧ e ∈ LinearMap.range (spectralMatrix D P).mulVecLin ∧
        l = (leftInverse D P).mulVec e) ∧
    ((∑ r, choiEigenvalueVector D P l r) = (n : ℂ) ↔ trivialCoefficient D l = 1) ∧
    ((∑ r, choiEigenvalueVector D P l r) = (n : ℂ) ↔ TracePreserving (spectralMap D l)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
