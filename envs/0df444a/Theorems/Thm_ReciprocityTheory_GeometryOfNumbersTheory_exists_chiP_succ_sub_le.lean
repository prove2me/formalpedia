-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_exists_chiP_succ_sub_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.exists_chiP_succ_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:08.226149+00:00
-- url     : https://prove2.me/theorems/130b864a-e15d-4c0e-b203-f65e4b005aae
-- title:
--   Geometry Of Numbers Theory: exists chi P succ sub le
-- statement:
--   The Geometry Of Numbers Theory construction uses the exists chi P succ sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L404-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L404-L480

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset

theorem ReciprocityTheory.GeometryOfNumbersTheory.exists_chiP_succ_sub_le (D : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := by sorry
