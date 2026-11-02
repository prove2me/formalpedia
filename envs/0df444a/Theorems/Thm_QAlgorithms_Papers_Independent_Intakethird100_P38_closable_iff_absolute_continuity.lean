-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_closable_iff_absolute_continuity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.closable_iff_absolute_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:27:19.628289+00:00
-- url     : https://prove2.me/theorems/31fa41d7-96b9-4627-9afe-84e11211144e
-- title:
--   Closability is equivalent to absolute continuity
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   For $\sigma\in\mathcal C$, put $q_\sigma(\psi)=\int|\widehat\psi|^2\,d\sigma$. Closability is taken in the ambient space $L^2(dx)$: whenever $s_k\in\mathcal S$ tends to zero in $L^2(dx)$ and $q_\sigma(s_k-s_l)\to0$ as both indices tend to infinity, one has $q_\sigma(s_k)\to0$. Then
--
--   $$q_\sigma\text{ is closable in }L^2(dx)\quad\Longleftrightarrow\quad\sigma\ll dx.$$
--
--   This keeps both implications, without assuming the existence of the source proof's auxiliary operator or kernel.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 12, Theorem 4.2: closability iff absolute continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Theorem 4.2, PDF pp.11--13: both directions of closability in the ambient
Lebesgue L2 space. The unfinished converse proof is not a premise. -/
theorem closable_iff_absolute_continuity (n : ℕ) (hn : 0 < n)
    (σ : Measure (SpectralDomain n)) (hσ : InC σ) :
    Closable (spectralQ σ) ↔ σ ≪ (volume : Measure (SpectralDomain n)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
