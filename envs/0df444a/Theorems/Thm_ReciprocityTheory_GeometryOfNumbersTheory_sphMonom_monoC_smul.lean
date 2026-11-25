-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_monoC_smul
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_monoC_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:35.965233+00:00
-- url     : https://prove2.me/theorems/531b16cf-29c5-4864-9175-e434da9bd7aa
-- title:
--   Geometry Of Numbers Theory: sph Monom mono C smul
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom mono C smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L187-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L187-L190

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_monoC_smul (a : Fin N → ℕ) (r : ℝ) (z : Fin N → ℂ) :
    monoC a (r • z) = (r : ℂ) ^ (∑ i, a i) * monoC a z := by sorry
