-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary21_pivotPhase
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.corollary21_pivotPhase
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:38:31.982049+00:00
-- url     : https://prove2.me/theorems/403aefdd-32a1-423d-8729-984f1610e6d9
-- title:
--   Corollary 21: phase freedom of pivot choices
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   For a fixed fine sector $r=(\alpha,i)$ and any two positive pivots $(s,t)$ and $(p,q)$, there is a real number $\zeta$ depending on both pivots such that
--
--   $$
--   V_r(p,q)=e^{i\zeta}V_r(s,t).\qquad (s,t)=(p,q)\ \Longrightarrow\ \text{one may take }\zeta=0.
--   $$
--
--   This describes the phase freedom of pivot choices in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 13, Corollary 21: phase freedom of pivot choices

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

/-- PDF p.13, Corollary 21 Eq.(64), with a phase depending on the two pivots. -/
theorem corollary21_pivotPhase (D : Data G A n) (r : Row D) (p q : Fin n × Fin n)
    (hp : 0 < pivotWeight D.U D.F r.1.val r.2 p)
    (hq : 0 < pivotWeight D.U D.F r.1.val r.2 q) :
    ∃ zeta : ℝ, (p = q → zeta = 0) ∧
      normalizedMatrix D.U D.F r.1.val r.2 q =
        phase zeta • normalizedMatrix D.U D.F r.1.val r.2 p := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
