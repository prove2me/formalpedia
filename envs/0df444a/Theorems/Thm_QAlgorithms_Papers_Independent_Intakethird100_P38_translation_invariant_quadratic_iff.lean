-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_translation_invariant_quadratic_iff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.translation_invariant_quadratic_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:23:22.36271+00:00
-- url     : https://prove2.me/theorems/53abc3f2-f601-4e0e-ad23-c6c04ef5c089
-- title:
--   Translation invariance characterizes spectral quadratic forms
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   Let $q:\mathcal S\to\mathbb R$ be continuous, nonnegative, satisfy $q(c\psi)=|c|^2q(\psi)$, and satisfy the parallelogram identity. Then
--
--   $$\left[\exists\sigma\in\mathcal C\;\forall\psi\in\mathcal S,\quad q(\psi)=\int|\widehat\psi|^2\,d\sigma\right]\quad\Longleftrightarrow\quad\left[\forall t\in\mathbb R^n\;\forall\psi\in\mathcal S,\quad q(\psi(\cdot-t))=q(\psi)\right].$$
--
--   This characterizes precisely the continuous positive quadratic forms represented by spectral measures.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 7, Lemma 3.2: translation-invariant continuous quadratic forms

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Lemma 3.2, PDF pp.7--8: all translations t are universally quantified.
The complex quadratic axioms are those explicitly given on p.6. -/
theorem translation_invariant_quadratic_iff (n : ℕ) (hn : 0 < n)
    (q : ComplexTest n → ℝ) (hq : PositiveQuadratic q) (hc : Continuous q) :
    (∃ σ : Measure (SpectralDomain n), InC σ ∧
      ∀ ψ : ComplexTest n, fourierEnergy σ ψ = ENNReal.ofReal (q ψ)) ↔
    (∀ (t : SpectralDomain n) (ψ : ComplexTest n), q (testTranslation t ψ) = q ψ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
