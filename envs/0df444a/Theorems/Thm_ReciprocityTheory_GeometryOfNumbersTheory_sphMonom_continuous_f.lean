-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_continuous_f
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_continuous_f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:08.847804+00:00
-- url     : https://prove2.me/theorems/f027e786-7e44-4317-8ac4-8c5a200b58eb
-- title:
--   Geometry Of Numbers Theory: sph Monom continuous f
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom continuous f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L198-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L198-L202

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_continuous_f (a b : Fin N → ℕ) :
    Continuous fun z : Fin N → ℂ => starRingEnd ℂ (monoC a z) * monoC b z := by sorry
