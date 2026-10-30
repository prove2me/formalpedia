-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_example56_probabilityLaw
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.example56_probabilityLaw
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:57:55.015417+00:00
-- url     : https://prove2.me/theorems/bebe92a4-191f-4790-8a20-5227971ca3de
-- title:
--   Example 56: every probability law on G supplies a channel
-- statement:
--   Let $G$ be a finite group and $U:G\to U(n)$ an ordinary unitary irreducible representation with $n>0$. Fix a complete family of inequivalent unitary irreducibles $\varphi^\alpha$, in fixed coordinate bases, with dimensions $d_\alpha>0$ and characters $\chi_\alpha$. Assume $U\otimes\overline U\simeq\bigoplus_{\alpha\in\Theta}\varphi^\alpha$, each occurring once. Throughout, $P_\alpha=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})\operatorname{Ad}_U(g)$, $\widetilde P_\alpha=\operatorname{mat}(P_\alpha)$, and $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ is unnormalized. Fine projectors use the diagonal matrix coefficient $\varphi^\alpha(g^{-1})_{ii}$ in place of the character. Whenever vectors $V_i^\beta$ occur, choose one pivot $(s,t)$ per fine sector with $p=(\widetilde P_{\beta i})_{st,st}>0$ and set $V_i^\beta=P_{\beta i}(E_{st})/\sqrt p$ and $v_i^\beta=\operatorname{vec}((V_i^\beta)^T)$. Write $\mu_i(\alpha,\beta)=(d_\alpha/|G|)\sum_g\chi_\alpha(g^{-1})|\operatorname{Tr}(V_i^\beta U(g)^\dagger)|^2$ and $M_{(\beta,i),\alpha}=\mu_i(\alpha,\beta)$ when these spectral coordinates occur.
--
--   For any probability law $p:G\to\mathbb R_{\ge0}$ with $\sum_gp(g)=1$, set $f(g)=|G|p(g)$. The character construction gives
--
--   $$
--   p(g)=\frac{f(g)}{|G|},\qquad l_\alpha=\frac1{d_\alpha}\sum_g\chi_\alpha(g)p(g),\qquad\Phi_p=\sum_{\alpha\in\Theta}l_\alpha P_\alpha\text{ is an ICQC}.
--   $$
--
--   This describes the every probability law on G supplies a channel in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 24, Example 56: every probability law on G supplies a channel

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

/-- PDF p.24, Example 56: f=|G|p and p=f/|G|; f alone is not a normalized law. -/
theorem example56_probabilityLaw (D : Data G A n) (p : G → ℝ)
    (hp : ∀ g, 0 ≤ p g) (hsum : ∑ g, p g = 1) :
    let f : G → ℂ := fun g => (Fintype.card G : ℂ) * (p g : ℂ)
    (∀ g, f g / Fintype.card G = (p g : ℂ)) ∧
    (∀ a : OccurringIrrep D, classCoefficients D f a =
      (∑ g, character (D.F.irrep a.val) g * (p g : ℂ)) / D.F.dim a.val) ∧
    IsIrrepCovariant D.U (spectralMap D (classCoefficients D f)) ∧
    IsPaperChannel (spectralMap D (classCoefficients D f)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
