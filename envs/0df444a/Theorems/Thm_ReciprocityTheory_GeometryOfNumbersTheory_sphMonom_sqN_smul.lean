-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_sqN_smul
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_sqN_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:29.143672+00:00
-- url     : https://prove2.me/theorems/e27fea47-080f-5ced-9d79-ff0ec7b1c1e2
-- title:
--   Geometry Of Numbers Theory: sph Monom sq N smul
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom sq N smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L204-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L204-L205

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_sqN_smul (c : ℂ) (z : Fin N → ℂ) : sqN (c • z) = ‖c‖ ^ 2 * sqN z := by sorry
