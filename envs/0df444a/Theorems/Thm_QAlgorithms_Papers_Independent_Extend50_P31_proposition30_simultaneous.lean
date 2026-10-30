-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition30_simultaneous
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.proposition30_simultaneous
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:44:50.472054+00:00
-- url     : https://prove2.me/theorems/0dc824d2-9a8e-4884-8417-b724fdcfac78
-- title:
--   Proposition 30 and Remarks 31–32: simultaneous Choi diagonalization
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   For the selected normalized matrices define $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$. No trace-preservation or real-character hypothesis is imposed. The eigenvalues do not depend on the positive pivots, and
--
--   $$
--   J(P_\alpha)v_i^\beta=\mu_i(\alpha,\beta)v_i^\beta,\qquad[J(P_\alpha),J(P_\gamma)]=0.
--   $$
--
--   This describes the simultaneous Choi diagonalization in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 15, Proposition 30 and Remarks 31–32: simultaneous Choi diagonalization

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

/-- PDF p.15, Proposition 30 and Remarks 31--32 Eqs.(76)--(78).
The modulus is squared, with no TP or real-character assumption. -/
theorem proposition30_simultaneous (D : Data G A n) (P : Pivots D) :
    (∀ a : OccurringIrrep D, ∀ r, (choi (centralMap D.U D.F a.val)).mulVec (choiVector D P r) =
      spectralMatrix D P r a • choiVector D P r) ∧
    (∀ a b : OccurringIrrep D, choi (centralMap D.U D.F a.val) * choi (centralMap D.U D.F b.val) =
      choi (centralMap D.U D.F b.val) * choi (centralMap D.U D.F a.val)) ∧
    (∀ a : A, ∀ r : Row D, ∀ p q,
      0 < pivotWeight D.U D.F r.1.val r.2 p → 0 < pivotWeight D.U D.F r.1.val r.2 q →
      muAt D a r p = muAt D a r q) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
