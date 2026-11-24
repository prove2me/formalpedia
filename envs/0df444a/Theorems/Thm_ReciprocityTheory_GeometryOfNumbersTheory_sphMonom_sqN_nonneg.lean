-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_sqN_nonneg
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_sqN_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:06.698436+00:00
-- url     : https://prove2.me/theorems/8320016f-d774-403f-b6e1-fbb4ba414c4a
-- title:
--   Geometry Of Numbers Theory: sph Monom sq N nonneg
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom sq N nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L94-L95

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_sqN_nonneg (z : Fin N → ℂ) : 0 ≤ sqN z := by sorry
