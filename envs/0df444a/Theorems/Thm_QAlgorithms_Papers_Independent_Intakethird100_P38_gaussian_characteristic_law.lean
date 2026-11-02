-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_gaussian_characteristic_law
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.gaussian_characteristic_law
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:22:42.168192+00:00
-- url     : https://prove2.me/theorems/39471bb4-3b0a-4665-869f-e02c39e015e9
-- title:
--   Gaussian measure on the continuous real tempered dual
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   For every $\sigma\in\mathcal C$ there exists a probability measure $\mu$ on $\Omega=\mathcal S(\mathbb R^n;\mathbb R)'$, the continuous real dual with its evaluation sigma-algebra, such that every real Schwartz test $\psi$ satisfies
--
--   $$\int_\Omega e^{i\omega(\psi)}\,d\mu(\omega)=\exp\!\left(-\frac12\int_{\mathbb R^n}|\widehat\psi(u)|^2\,d\sigma(u)\right).$$
--
--   This constructs the distribution Gaussian law, including the Dirac law at zero when $\sigma=0$. No symmetry of $\sigma$ is assumed.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 3, §1(d), unnumbered: distribution Gaussian characteristic law

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- §1(d), PDF p.3 (standing assumptions pp.2--6): existence of the distribution
Gaussian law. Includes σ=0, and assumes no reflection symmetry. -/
theorem gaussian_characteristic_law (n : ℕ) (hn : 0 < n)
    (σ : Measure (SpectralDomain n)) (hσ : InC σ) :
    ∃ μ : Measure (Omega n), CharacteristicLaw σ μ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
