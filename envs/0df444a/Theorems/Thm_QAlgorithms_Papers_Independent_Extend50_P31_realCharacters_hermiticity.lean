-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_realCharacters_hermiticity
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.realCharacters_hermiticity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:48:55.534285+00:00
-- url     : https://prove2.me/theorems/858180c6-0dee-4d1e-9921-710ed1131b10
-- title:
--   Unnumbered consequence after Lemma 39: real-character Hermiticity
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   Assume every irreducible character of $G$ is real-valued. Then the Choi images of the computed occurring projectors are Hermitian and all their eigenvalues are real:
--
--   $$
--   J(P_\alpha)^\dagger=J(P_\alpha),\qquad\mu_i(\alpha,\beta)\in\mathbb R\qquad(\alpha,\beta\in\Theta,\ 1\le i\le d_\beta).
--   $$
--
--   This describes the real-character Hermiticity in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 17, Unnumbered consequence after Lemma 39: real-character Hermiticity

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

/-- PDF p.17, consequence of Eqs.(85),(86); coefficient reality is not asserted. -/
theorem realCharacters_hermiticity (D : Data G A n) (P : Pivots D)
    (hreal : ∀ a : A, ∀ g : G, (character (D.F.irrep a) g).im = 0) :
    (∀ a : OccurringIrrep D, (choi (centralMap D.U D.F a.val)).IsHermitian) ∧
    ∀ a : OccurringIrrep D, ∀ r, (spectralMatrix D P r a).im = 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
