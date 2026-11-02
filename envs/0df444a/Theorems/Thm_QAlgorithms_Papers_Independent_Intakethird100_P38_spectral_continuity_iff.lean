-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_spectral_continuity_iff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.spectral_continuity_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:23:59.287823+00:00
-- url     : https://prove2.me/theorems/0ff655c7-66d5-450b-87f0-3ae2e837d16f
-- title:
--   Continuity characterizes the spectral growth class
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   For a regular positive Borel measure $\sigma$ not initially assumed in $\mathcal C$, define the nonnegative extended integral $Q_\sigma(\psi)=\int|\widehat\psi|^2\,d\sigma$. Then
--
--   $$\sigma\in\mathcal C\quad\Longleftrightarrow\quad Q_\sigma(\psi)<\infty\ \text{for every }\psi\in\mathcal S,\quad\text{and }\psi\mapsto Q_\sigma(\psi)\text{ is real-valued and continuous}.$$
--
--   The finiteness clause spells out what it means for the printed map to be a continuous real-valued quadratic form.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 8, Proposition 3.3: continuity characterizes C

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Proposition 3.3, PDF pp.8--9: finiteness is explicit before continuity of the
real-valued form, so a divergent nonnegative integral cannot become zero. -/
theorem spectral_continuity_iff (n : ℕ) (hn : 0 < n)
    (σ : Measure (SpectralDomain n)) (hregular : σ.Regular) :
    InC σ ↔ ((∀ ψ : ComplexTest n, fourierEnergy σ ψ < ⊤) ∧ Continuous (spectralQ σ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
