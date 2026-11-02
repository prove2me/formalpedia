-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_gaussian_ergodicity_iff_point_spectrum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.gaussian_ergodicity_iff_point_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:29:16.432391+00:00
-- url     : https://prove2.me/theorems/526fd766-949c-4e20-b623-a7977bc593cb
-- title:
--   Ergodicity and the point spectrum of the Gaussian action
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   Let $\sigma\in\mathcal C$, let $\mu$ have the real characteristic functional of §1(d), and let $U$ be the full complex $L^2(\mu)$ Koopman group of distribution shifts $\theta_t\omega(\psi)=\omega(\psi(\cdot+t))$. Then
--
--   $$\text{the shift action is ergodic}\quad\Longleftrightarrow\quad\begin{cases}\text{every nonzero joint eigenvector has frequency }a=0,\\\{f:U(t)f=f\ \forall t\}=\mathbb C\mathbf1.\end{cases}$$
--
--   Frequency $a\in\mathbb R^n$ means $U(t)f=e^{ia\cdot t}f$ for every $t$. Ergodicity means that every measurable set invariant modulo null sets under all shifts has probability zero or one. The fixed space has complex dimension one, including when $\sigma=0$.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 19, Theorem 8.3: ergodicity and point spectrum

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Theorem 8.3, PDF pp.19--20: in this Gaussian distribution regime, ergodicity
is equivalent to absence of nonzero frequencies together with the one-dimensional
constant fixed space. This is not asserted for arbitrary probability actions. -/
theorem gaussian_ergodicity_iff_point_spectrum (n : ℕ) (hn : 0 < n)
    (σ : Measure (SpectralDomain n)) (hσ : InC σ)
    (μ : Measure (Omega n)) (hμ : CharacteristicLaw σ μ)
    (U : KoopmanFamily μ) (hU : IsKoopman μ U) :
    TrivialPointSpectrum μ U ↔ ShiftErgodic μ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
