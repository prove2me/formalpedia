-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition20_eigenmatrices
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.proposition20_eigenmatrices
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:37:23.254087+00:00
-- url     : https://prove2.me/theorems/b0597ab9-6fb7-45f7-bfb1-f94f78c8015b
-- title:
--   Proposition 20: explicit normalized eigenmatrices
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Write $r=(\alpha,i)$ for a fine sector, set $W_r(s,t)=P_r(E_{st})$ and $p_r(s,t)=(\widetilde P_r)_{st,st}$. Every sector has a pivot with $p_r(s,t)>0$. For every such pivot set $V_r(s,t)=W_r(s,t)/\sqrt{p_r(s,t)}$. These matrices have Hilbert–Schmidt norm one, satisfy the fine eigenmatrix equations, and any unit eigenmatrix in the range of $P_r$ is one of them up to a unit phase. For valid pivots and a real phase $\zeta$,
--
--   $$
--   P_qV_r=\delta_{qr}V_r,\qquad (V_r(s,t),V_q(u,v))=\delta_{rq}e^{i\zeta}.
--   $$
--
--   The raw matrices and the normalized matrices are different objects. No rank or norm statement is assumed as input; these are conclusions of the construction.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 13, Proposition 20: explicit normalized eigenmatrices

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

/-- PDF p.13, Proposition 20 Eqs.(61)--(63). Eq.(62) constructs normalized representatives;
an arbitrary unit eigenmatrix is one of these up to phase. Eq.(67) instead concerns raw matrices. -/
theorem proposition20_eigenmatrices (D : Data G A n) :
    (∀ r : Row D, ∃ p : Fin n × Fin n, 0 < pivotWeight D.U D.F r.1.val r.2 p) ∧
    (∀ r : Row D, ∀ p, 0 < pivotWeight D.U D.F r.1.val r.2 p →
      hs (normalizedMatrix D.U D.F r.1.val r.2 p) (normalizedMatrix D.U D.F r.1.val r.2 p) = 1 ∧
      ∀ s : Row D, fineMap D.U D.F s.1.val s.2 (normalizedMatrix D.U D.F r.1.val r.2 p) =
        if s = r then normalizedMatrix D.U D.F r.1.val r.2 p else 0) ∧
    (∀ r s : Row D, ∀ p q,
      0 < pivotWeight D.U D.F r.1.val r.2 p → 0 < pivotWeight D.U D.F s.1.val s.2 q →
      ∃ zeta : ℝ, hs (normalizedMatrix D.U D.F r.1.val r.2 p)
        (normalizedMatrix D.U D.F s.1.val s.2 q) = if r = s then phase zeta else 0) ∧
    (∀ r : Row D, ∀ X : Mat n, hs X X = 1 → fineMap D.U D.F r.1.val r.2 X = X →
      ∃ p : Fin n × Fin n, 0 < pivotWeight D.U D.F r.1.val r.2 p ∧
        ∃ zeta : ℝ, X = phase zeta • normalizedMatrix D.U D.F r.1.val r.2 p) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
