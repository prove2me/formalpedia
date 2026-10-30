-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_remarks27_36_trace
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.remarks27_36_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:43:20.654378+00:00
-- url     : https://prove2.me/theorems/4584b683-a952-42de-80db-d20eea6ef71b
-- title:
--   Remarks 27 and 36: Choi trace and total eigenvalue sum
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   For a trace-preserving $\Phi_l$, let $\epsilon_i^\beta$ be its Choi eigenvalues in the selected common eigenbasis, including every fine-sector multiplicity. Then
--
--   $$
--   \operatorname{Tr}J(\Phi_l)=n,\qquad\sum_{\beta\in\Theta}\sum_{i=1}^{d_\beta}\epsilon_i^\beta=n.
--   $$
--
--   This describes the Choi trace and total eigenvalue sum in the fixed source conventions.
--
--   **Formalization Note** The trivial coefficient is extracted by summing the coefficient at the trivial label, without assuming in the input data the theorem that this label occurs.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 14, Remarks 27 and 36: Choi trace and total eigenvalue sum

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

/-- PDF pp.14,16, Remarks 27 and 36 Eqs.(73),(81), on the TP domain. -/
theorem remarks27_36_trace (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ)
    (hl : trivialCoefficient D l = 1) :
    Matrix.trace (choi (spectralMap D l)) = (n : ℂ) ∧
    (∑ r : Row D, choiEigenvalueVector D P l r) = (n : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
