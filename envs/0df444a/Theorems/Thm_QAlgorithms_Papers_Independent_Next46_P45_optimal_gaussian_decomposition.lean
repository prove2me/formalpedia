-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P45_optimal_gaussian_decomposition
-- name    : QAlgorithms.Papers.Independent.Next46.P45.optimal_gaussian_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:52:03.25799+00:00
-- url     : https://prove2.me/theorems/91f7abc1-2add-4672-9896-226a7d48347c
-- title:
--   An optimal displaced pure Gaussian ensemble
-- statement:
--   Let $\sigma$ be an actual symmetric two-mode Gaussian density in the standard-form convention of Proposition 2, with $\Gamma=\operatorname{standard}(n,n,k_x,-k_p)$ and $k_x\ge k_p\ge0$. All moments are finite, the full uncertainty inequality holds, and first moments are arbitrary. Set $t=\min\{1,\sqrt{(n-k_x)(n-k_p)}\}$ and $r_t=-\frac12\ln t$. There exist local full-space unitaries $U_A,U_B$ and a centered normalized pure Gaussian seed $\phi=(U_A\otimes U_B)\Psi_s(r_t)$ of covariance $\Gamma_0$, together with a possibly degenerate Gaussian probability measure $\mu$ on real first-moment shifts $x\in\mathbb R^4$, and a measurable family $\phi_x=D(x)\phi$ of normalized Gaussian pure states, such that
--
--   $$\sigma=\int |\phi_x\rangle\langle\phi_x|\,d\mu(x),\qquad \int E(\phi_x)\,d\mu(x)=E_F(\sigma).$$
--
--   Every member has covariance $\Gamma_0$ and entanglement $E(\Psi_s(r_t))$. The shifts use $z_j=(x_{q_j}+i x_{p_j})/\sqrt2$ in $D(z_j)=\exp(z_ja_j^\dagger-\overline z_ja_j)$. The probability law has mean $m$ and classical covariance $(\Gamma-\Gamma_0)/2$, equivalently characteristic function $\exp(i v^Tm-v^T(\Gamma-\Gamma_0)v/4)$. The residual is positive semidefinite and may vanish; a Dirac law is included. Thus this Gaussian ensemble attains the infimum over all pure-state decompositions. This assertion is restricted to symmetric Gaussian states.
-- source:
--   Entanglement of formation for symmetric Gaussian states, arXiv:quant-ph/0304042v1, PDF p. 4, Unnumbered attainment of E_F by the displaced squeezed-state Gaussian ensemble D_0

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne IsBarycenter)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance standardFormCovariance productWeyl
   CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits InterleavedPhase)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF pp.1,3–4, optimal D_0: an actual Gaussian probability ensemble attains
the unrestricted E_F. The centered pure Gaussian seed is locally equivalent to
the selected squeezed state; its displacements shift actual first moments by x.
Correction to the printed density: permit a semidefinite residual and a Dirac
law rather than its nonexistent four-dimensional inverse-covariance density.
The separable branch uses the vacuum seed (up to local unitary squeezing). -/
theorem optimal_gaussian_decomposition
    (rho : DensityKernel 2) (n kx kp : ℝ) (hkp : 0 ≤ kp) (hk : kp ≤ kx)
    (hphysical : GaussianWithCovariance rho (standardFormCovariance n n kx (-kp))) :
    ∃ (U V : Hilbert ℕ ≃ₗᵢ[ℂ] Hilbert ℕ) (seed : PureVector)
      (Gseed : Cov 2) (m : (InterleavedPhase 2)) (mu : Measure (InterleavedPhase 2)) (psi : (InterleavedPhase 2) → PureVector),
      (∀ i, seed.val i = localSeedCoefficients U V (squeezingAt (symmetricEprLevel n kx kp)) i) ∧
      GaussianWithCovariance (rankOne seed.val) Gseed ∧
      (∀ v, CharacteristicSummable (rankOne seed.val) v ∧
        multimodeWeylTrace (rankOne seed.val) v = covarianceCharacteristicValue Gseed 0 v) ∧
      GaussianShiftLaw mu m (standardFormCovariance n n kx (-kp) - Gseed) ∧
      Measurable psi ∧
      (∀ x i, (psi x).val i = shiftedCoefficients x seed.val i) ∧
      (∀ x, GaussianWithCovariance (rankOne (psi x).val) Gseed) ∧
      Decomposes (mu.map psi) rho ∧
      (∀ x, pureEntanglement (psi x).val =
        pureEntanglement (squeezedVector (squeezingAt (symmetricEprLevel n kx kp)))) ∧
      ensembleCost (mu.map psi) = entanglementOfFormation rho := by sorry

end QAlgorithms.Papers.Independent.Next46.P45

end
