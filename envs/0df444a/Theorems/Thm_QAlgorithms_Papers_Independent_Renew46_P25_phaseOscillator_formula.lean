-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P25_phaseOscillator_formula
-- name    : QAlgorithms.Papers.Independent.Renew46.P25.phaseOscillator_formula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:41:25.432343+00:00
-- url     : https://prove2.me/theorems/53e3a3e5-e23d-46b0-9de4-d544335a76db
-- title:
--   Phase-space harmonic oscillator
-- statement:
--   Let $n\ge1$, $z=(x,p)\in\mathbb R^{2n}$, and $F\in\mathcal S(\mathbb R^{2n})$. For the harmonic-oscillator symbol $H(x,p)=\frac12(|x|^2+|p|^2)$, its polynomial Weyl quantization is $\widehat H_{\rm ph}=\frac12\sum_j(\widehat x_{{\rm ph},j}^{\,2}+\widehat p_{{\rm ph},j}^{\,2})$, where $\widehat x_{{\rm ph},j}=x_j/2+i\partial_{p_j}$ and $\widehat p_{{\rm ph},j}=p_j/2-i\partial_{x_j}$. It satisfies
--
--   $$\widehat H_{\rm ph}F(z)=-\tfrac12\Delta_zF(z)-\tfrac i2\sum_j\bigl(p_j\partial_{x_j}-x_j\partial_{p_j}\bigr)F(z)+\tfrac18|z|^2F(z).$$
--
--   Here $\Delta_z$ is the Laplacian in all $2n$ real coordinates. Pure coordinate squares have no Weyl-ordering ambiguity; this is the differential operator in Example 17.
-- source:
--   A Weyl Calculus on Symplectic Phase Space, arXiv:math-ph/0508024v2, PDF p. 33, Example 17 (82)–(83): phase-space harmonic oscillator

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25

noncomputable section

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

namespace QAlgorithms.Papers.Independent.Renew46.P25

/-- PDF p.33, Example 17, (82)-(83): the phase-space Weyl harmonic oscillator
is -Delta/2-i sigma(z,partial_z)/2+|z|^2/8 on Schwartz input. -/
theorem phaseOscillator_formula (n : ℕ) (hn : 0 < n)
    (F : SchwartzMap (PhaseSpaceGrouped n) ℂ) (z : PhaseSpaceGrouped n) :
    phaseOscillator F z = -(1 / 2 : ℂ) * phaseLaplacian F z -
      (Complex.I / 2) * phaseAngularDerivative F z +
      (((∑ k : Phase n, z k ^ 2) / 8 : ℝ) : ℂ) * F z := by sorry

end QAlgorithms.Papers.Independent.Renew46.P25

end
