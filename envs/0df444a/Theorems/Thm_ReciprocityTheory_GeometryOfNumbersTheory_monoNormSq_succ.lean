-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_succ
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.monoNormSq_succ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:22.279254+00:00
-- url     : https://prove2.me/theorems/c79bb54d-353d-40f2-8b72-a3dcb4c768bb
-- title:
--   Geometry Of Numbers Theory: mono Norm Sq succ
-- statement:
--   The Geometry Of Numbers Theory construction uses the mono Norm Sq succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L95-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L95-L117

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.monoNormSq_succ {D : ℕ} (a : Fin (D + 1) → ℕ) :
    monoNormSq (Function.update a 0 (a 0 + 1)) =
      monoNormSq a * ((a 0 + 1 : ℝ) / ((∑ i, a i : ℕ) + D + 1 : ℝ)) := by sorry
