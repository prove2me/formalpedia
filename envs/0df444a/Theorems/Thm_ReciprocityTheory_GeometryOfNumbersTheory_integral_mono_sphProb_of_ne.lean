-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_mono_sphProb_of_ne
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.integral_mono_sphProb_of_ne
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:02.247873+00:00
-- url     : https://prove2.me/theorems/d47ffd65-5bc7-4756-81f0-f34f1c05f8b0
-- title:
--   Geometry Of Numbers Theory: integral mono sph Prob of ne
-- statement:
--   The Geometry Of Numbers Theory construction uses the integral mono sph Prob of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomSt.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomSt.lean#L24-L37

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.integral_mono_sphProb_of_ne {D : ℕ} {a b : Fin (D + 1) → ℕ} (hab : a ≠ b) :
    ∫ z, starRingEnd ℂ (monoC a z) * monoC b z ∂(sphProb (D + 1)) = 0 := by sorry
