-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_theorem58_rawIdentities
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.theorem58_rawIdentities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:03:46.539681+00:00
-- url     : https://prove2.me/theorems/ae21c23b-8161-408a-92cf-4daef8ebd00f
-- title:
--   Theorem 58: norm, reconstruction and trace identities for raw eigenmatrices
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   For occurring fine sectors $r=(\alpha,i)$, use the raw matrices $W_r(s,t)=P_r(E_{st})$, without normalizing and including zero pivots. Their norm, reconstruction and trace identities are
--
--   $$
--   \begin{gathered}\|W_r(s,t)\|_{\mathrm{HS}}^2=(\widetilde P_r)_{st,st},\qquad\sum_{s,t}\|W_r(s,t)\|_{\mathrm{HS}}^2=1,\\\sum_r W_r(s,t)=E_{st},\qquad\sum_sW_{\alpha i}(s,s)=\delta_{\alpha,\mathrm{id}}I_n,\qquad\operatorname{Tr}W_{\alpha i}(s,t)=\delta_{\alpha,\mathrm{id}}\delta_{st}.\end{gathered}
--   $$
--
--   This describes the norm, reconstruction and trace identities for raw eigenmatrices in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 31, Theorem 58: norm, reconstruction and trace identities for raw eigenmatrices

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

/-- PDF pp.31--32, Theorem 58 Eqs.(157)--(160), proof p.40 Eq.(192).
SOURCE CORRECTION: these are raw W, not normalized Eq.(62) V. At id and a diagonal
pivot, W=I/n has squared HS norm 1/n. Proof Eq.(194) also needs the omitted sum over s. -/
theorem theorem58_rawIdentities (D : Data G A n) :
    (∀ r : Row D, ∀ p : Fin n × Fin n,
      hs (rawMatrix D.U D.F r.1.val r.2 p) (rawMatrix D.U D.F r.1.val r.2 p) =
        fineMatrix D.U D.F r.1.val r.2 p p) ∧
    (∀ r : Row D, (∑ p : Fin n × Fin n,
      hs (rawMatrix D.U D.F r.1.val r.2 p) (rawMatrix D.U D.F r.1.val r.2 p)) = 1) ∧
    (∀ p : Fin n × Fin n, (∑ r : Row D, rawMatrix D.U D.F r.1.val r.2 p) = matrixUnit p.1 p.2) ∧
    (∀ r : Row D, (∑ s : Fin n, rawMatrix D.U D.F r.1.val r.2 (s,s)) =
      if r.1.val = D.F.trivial then 1 else 0) ∧
    (∀ r : Row D, ∀ p : Fin n × Fin n, Matrix.trace (rawMatrix D.U D.F r.1.val r.2 p) =
      if r.1.val = D.F.trivial ∧ p.1 = p.2 then 1 else 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
