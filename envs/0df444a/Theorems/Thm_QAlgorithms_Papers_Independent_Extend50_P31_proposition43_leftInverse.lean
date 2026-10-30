-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition43_leftInverse
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.proposition43_leftInverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:51:14.458946+00:00
-- url     : https://prove2.me/theorems/3bcc25f8-2482-45c1-b5a1-cd14fee36481
-- title:
--   Proposition 43: full column rank and canonical left inverse
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Let $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$, with $n^2$ rows and $|\Theta|$ columns, and form its Gram matrix $H=M^\dagger M$. Then its columns are linearly independent, $H$ is invertible, and
--
--   $$
--   \operatorname{rank}M=|\Theta|,\qquad M_{\mathrm{inv}}=H^{-1}M^\dagger,\qquad M_{\mathrm{inv}}M=I_{|\Theta|}.
--   $$
--
--   This describes the full column rank and canonical left inverse in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 19, Proposition 43: full column rank and canonical left inverse

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

/-- PDF p.19, Proposition 43 Eqs.(96)--(98); M is rectangular and Gram invertibility is concluded. -/
theorem proposition43_leftInverse (D : Data G A n) (P : Pivots D) :
    Matrix.rank (spectralMatrix D P) = Fintype.card (OccurringIrrep D) ∧
    LinearIndependent ℂ (fun a : OccurringIrrep D => fun r : Row D => spectralMatrix D P r a) ∧
    IsUnit (spectralGram D P) ∧
    leftInverse D P * spectralMatrix D P = 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
