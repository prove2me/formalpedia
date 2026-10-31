-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P74_constellation_moment_matching
-- name    : QAlgorithms.Papers.Independent.Intake100.P74.constellation_moment_matching
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:58:11.500313+00:00
-- url     : https://prove2.me/theorems/b2aad717-78c8-4ff9-9311-61c2d27cce09
-- title:
--   Constellation first and second quantum moments
-- statement:
--   Let $N\ge0$. Let $X$ and $Y$ be independent finite real laws, each on at least two indexed points, with nonnegative weights summing to one, mean zero, and second moment one. Set $Z=\sqrt{N/2}(X+iY)$ and $\rho=\mathbb E[|Z\rangle\langle Z|]$ on the full single-mode Fock space. Then $\rho$ is a normalized density operator and has the same first and second moments as the thermal state $\tau_N$:
--
--   $$
--   \langle a\rangle=\langle a^\dagger\rangle=\langle a^2\rangle=\langle (a^\dagger)^2\rangle=0,\qquad
--   \langle a^\dagger a\rangle=N,\quad\langle aa^\dagger\rangle=N+1.
--   $$
--
--   All six expectation series converge, and the mean photon number is $N$. This gives the quantum moment matching used by the information-gap argument. At $N=0$ the mixture is vacuum.
-- source:
--   Coherent-state constellations and polar codes for thermal Gaussian channels, arXiv:1603.05970v3, PDF p. 5, §4 (7)–(8): input first and second moments

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

/-- PDF p.5, (7)--(8): independent normalized centered variance-one finite
laws give all first and second quantum moments of tau_N and photon energy N.
Named constellations have m>=2. No channel assumption is needed for this input
identity; N=0 gives vacuum. Cross moments include both a†a and aa†. -/
theorem constellation_moment_matching
    (m l : ℕ) (hm : 2 ≤ m) (hl : 2 ≤ l) (N : ℝ) (hN : 0 ≤ N)
    (p : Fin m → ℝ) (q : Fin l → ℝ) (x : Fin m → ℝ) (y : Fin l → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpTotal : ∑ i, p i = 1) (hqTotal : ∑ j, q j = 1)
    (hxMean : ∑ i, p i * x i = 0) (hyMean : ∑ j, q j * y j = 0)
    (hxVariance : ∑ i, p i * (x i) ^ 2 = 1)
    (hyVariance : ∑ j, q j * (y j) ^ 2 = 1) :
    IsDensity (finiteConstellationState N p q x y) ∧
    HasThermalMoments (finiteConstellationState N p q x y) N ∧
    HasThermalMoments (thermalMatrix (2 * N + 1)) N ∧
    photonEnergy (fun a b : Fin 1 → ℕ =>
      finiteConstellationState N p q x y (a 0) (b 0)) = ENNReal.ofReal N := by sorry

end QAlgorithms.Papers.Independent.Intake100.P74

end
