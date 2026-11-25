-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_finrank_sphMonomE
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.finrank_sphMonomE
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:53:31.106911+00:00
-- url     : https://prove2.me/theorems/7e79e8bf-bfd3-526f-b015-49d80b37db82
-- title:
--   Geometry Of Numbers Theory: finrank sph Monom E
-- statement:
--   The Geometry Of Numbers Theory construction uses the finrank sph Monom E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L84-L86

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
variable (N : ℕ)

theorem ReciprocityTheory.GeometryOfNumbersTheory.finrank_sphMonomE : Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) = 2 * N := by sorry
