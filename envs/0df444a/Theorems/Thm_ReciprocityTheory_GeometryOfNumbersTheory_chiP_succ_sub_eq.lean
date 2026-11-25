-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiP_succ_sub_eq
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiP_succ_sub_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:08.591802+00:00
-- url     : https://prove2.me/theorems/8a978e4e-4e1c-428c-91c7-a487ec9d5c41
-- title:
--   Geometry Of Numbers Theory: chi P succ sub eq
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi P succ sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L211-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L211-L226

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiP_succ_sub_eq (D n : ℕ) :
    chiP D (n + 1) - chiP D n = (1 / 2) *
      (∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) +
       ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
          -Real.log (monoNormSq b)) := by sorry
