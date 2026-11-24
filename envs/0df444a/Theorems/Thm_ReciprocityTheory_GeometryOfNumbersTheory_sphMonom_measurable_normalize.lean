-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_measurable_normalize
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_measurable_normalize
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:19.733565+00:00
-- url     : https://prove2.me/theorems/c4132533-08eb-46b3-9fc3-b59a59ecbb0d
-- title:
--   Geometry Of Numbers Theory: sph Monom measurable normalize
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom measurable normalize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L164-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L164-L166

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_measurable_normalize :
    Measurable (fun z : Fin N → ℂ => (((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z) := by sorry
