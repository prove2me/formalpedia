-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphProb_compl_sphere
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphProb_compl_sphere
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:22.544857+00:00
-- url     : https://prove2.me/theorems/8807637d-5c01-4a8d-a108-19bd274e8a7a
-- title:
--   Geometry Of Numbers Theory: sph Prob compl sphere
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Prob compl sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomSt.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomSt.lean#L11-L22

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphProb_compl_sphere (D : ℕ) : sphProb (D + 1) {z | sqN z = 1}ᶜ = 0 := by sorry
