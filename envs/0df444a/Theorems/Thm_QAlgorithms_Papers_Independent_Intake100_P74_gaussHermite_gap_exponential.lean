-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P74_gaussHermite_gap_exponential
-- name    : QAlgorithms.Papers.Independent.Intake100.P74.gaussHermite_gap_exponential
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:03:14.549889+00:00
-- url     : https://prove2.me/theorems/9e2bba32-fd8f-40da-936c-afaf3b9ccd49
-- title:
--   Exponential Gauss-Hermite thermal-channel gap
-- statement:
--   Fix $0\le k\le1$, $N_c\ge0$ and finite $N>0$. For each $m\ge2$, let $X_m$ be standard-normal Gauss-Hermite quadrature: its nodes are the $m$ roots of the probabilists' Hermite polynomial $H_m$ and the weight at a root $x$ is $m!/(m^2H_{m-1}(x)^2)$. Use independent copies as the two coordinates of $Z_m=\sqrt{N/2}(X_m+iX'_m)$, and let $\rho_m$ be the actual average thermal-channel output. Set $N'=k^2N+N_c$ and $\Delta_B(m)=g(N')-H(\rho_m)$ in nats. For $k>0$, define $s=k^2N/(\sqrt{N'(N'+1)}-k^2N)$ and $c=2\log((1+s)/s)>0$. Then
--
--   $$\exists C>0\;\exists m_0\ge2\;\forall m\ge m_0:\quad \Delta_B(m)\le C e^{-cm}.$$
--
--   The constants may depend on the fixed channel and energy, and never on $m$. For $k=0$ the gap is zero for every $m\ge2$. There are $m^2$ complex coherent signals. This controls convergence at fixed energy and does not assert an energy-uniform prefactor or an efficient decoder.
-- source:
--   Coherent-state constellations and polar codes for thermal Gaussian channels, arXiv:1603.05970v3, PDF p. 6, §4: exponential thermal-channel Gauss–Hermite gap

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P74

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P74

open MeasureTheory

open scoped BigOperators ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient thermalMatrix)

open QAlgorithms.Papers.Independent.Support50.P14 (photonEnergy)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal spectralEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P39 (thermalProbability g)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.5--6: Gauss--Hermite thermal-channel gap. The physical channel
and finite positive energy are fixed before C and m0; m varies afterward.
k=0 is stated separately. No high-energy uniform prefactor is asserted. -/
theorem gaussHermite_gap_exponential
    (k Nc N : ℝ) (hk : 0 ≤ k) (hkUpper : k ≤ 1) (hNc : 0 ≤ Nc) (hN : 0 < N) :
    (0 < k → 0 < gapExponent k Nc N ∧
      ∃ C : ℝ, 0 < C ∧ ∃ m0 : ℕ, 2 ≤ m0 ∧ ∀ m ≥ m0,
        classicalInformationGap k Nc N (gaussHermiteLaw m) ≤
          ENNReal.ofReal (C * Real.exp (-gapExponent k Nc N * (m : ℝ)))) ∧
    (k = 0 → ∀ m ≥ 2, classicalInformationGap k Nc N (gaussHermiteLaw m) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P74

end
