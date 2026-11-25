-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_mono_sq_sphProb
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.integral_mono_sq_sphProb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:52:59.342856+00:00
-- url     : https://prove2.me/theorems/907b26ba-457b-5507-907b-438324e783d3
-- title:
--   Geometry Of Numbers Theory: integral mono sq sph Prob
-- statement:
--   The Geometry Of Numbers Theory construction uses the integral mono sq sph Prob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomSt.lean#L39-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomSt.lean#L39-L68

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.integral_mono_sq_sphProb {D : ℕ} (a : Fin (D + 1) → ℕ) :
    ∫ z, ‖monoC a z‖ ^ 2 ∂(sphProb (D + 1)) = monoNormSq a := by sorry
