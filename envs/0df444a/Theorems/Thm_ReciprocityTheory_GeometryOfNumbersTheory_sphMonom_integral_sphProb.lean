-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_integral_sphProb
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_integral_sphProb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:29.070874+00:00
-- url     : https://prove2.me/theorems/5f3aeeca-b198-45cc-989e-647b8a0e5500
-- title:
--   Geometry Of Numbers Theory: sph Monom integral sph Prob
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom integral sph Prob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L168-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L168-L185

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable {N : ℕ}

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_integral_sphProb (g : (Fin N → ℂ) → ℂ) (hg : Continuous g) :
    ∫ z, g z ∂(sphProb N) =
      ((Real.pi ^ N)⁻¹ : ℂ) * ∫ z, g ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ) := by sorry
