-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_f_smul
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_f_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:23.5141+00:00
-- url     : https://prove2.me/theorems/d4dd7cf3-f733-414a-82bf-e59b2f6a9696
-- title:
--   Geometry Of Numbers Theory: sph Monom f smul
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom f smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L192-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L192-L196

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_f_smul (a b : Fin N → ℕ) (r : ℝ) (z : Fin N → ℂ) :
    starRingEnd ℂ (monoC a (r • z)) * monoC b (r • z) =
      (r : ℂ) ^ ((∑ i, a i) + ∑ i, b i) * (starRingEnd ℂ (monoC a z) * monoC b z) := by sorry
