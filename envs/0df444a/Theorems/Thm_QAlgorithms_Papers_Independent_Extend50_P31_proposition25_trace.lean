-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition25_trace
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.proposition25_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:41:14.474983+00:00
-- url     : https://prove2.me/theorems/417e7c4d-63ea-4a1c-9504-ef9e330d8c18
-- title:
--   Proposition 25: trace preservation fixes exactly the trivial coefficient
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   For arbitrary complex coefficients $l_\alpha$, put $\Phi_l=\sum_{\alpha\in\Theta}l_\alpha P_\alpha$. No positivity or adjoint-preservation hypothesis is needed for
--
--   $$
--   \Phi_l\text{ preserves trace on every operator}\quad\Longleftrightarrow\quad l_{\mathrm{id}}=1.
--   $$
--
--   This describes the trace preservation fixes exactly the trivial coefficient in the fixed source conventions.
--
--   **Formalization Note** The trivial coefficient is extracted by summing the coefficient at the trivial label, without assuming in the input data the theorem that this label occurs.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 14, Proposition 25: trace preservation fixes exactly the trivial coefficient

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

/-- PDF p.14, Proposition 25 Eq.(70). No positivity or Hermitian preservation is assumed. -/
theorem proposition25_trace (D : Data G A n) (l : OccurringIrrep D → ℂ) :
    TracePreserving (spectralMap D l) ↔ trivialCoefficient D l = 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
