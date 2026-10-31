-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P24_stokes_positivity_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P24.stokes_positivity_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:12:45.682664+00:00
-- url     : https://prove2.me/theorems/eb9eb0f6-e195-452c-b732-34e584f15ae8
-- title:
--   Positivity bounds the Stokes vector
-- statement:
--   Let $s_0,s_1,s_2,s_3$ be real Stokes parameters and let $\sigma_x,\sigma_y,\sigma_z$ be the Pauli matrices. If the unnormalized Stokes matrix $S=(s_0I+s_1\sigma_x+s_2\sigma_y+s_3\sigma_z)/2$ is positive semidefinite, then
--
--   $$s_1^2+s_2^2+s_3^2\le s_0^2.$$
--
--   This is the intensity-dependent positivity constraint on polarization parameters.
-- source:
--   Quantum features of macroscopic fields. Entropy and dynamics, arXiv:1904.06170v1, PDF p. 2, §II, (2)–(3): Stokes positivity bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩

/-- arXiv:1904.06170v1 PDF p.2, (2)–(3): positivity of the Stokes matrix
implies the Stokes-vector bound. Intensity is not normalized. -/
theorem stokes_positivity_bound (s0 s1 s2 s3 : ℝ)
    (hS : (stokesMatrix s0 s1 s2 s3).PosSemidef) :
    s1 ^ 2 + s2 ^ 2 + s3 ^ 2 ≤ s0 ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P24

end
