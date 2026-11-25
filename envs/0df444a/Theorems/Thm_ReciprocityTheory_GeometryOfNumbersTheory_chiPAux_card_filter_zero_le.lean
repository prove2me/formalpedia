-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_card_filter_zero_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_card_filter_zero_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:48.421537+00:00
-- url     : https://prove2.me/theorems/d27ea380-9daf-426a-a075-4f7b4e9f636a
-- title:
--   Geometry Of Numbers Theory: chi PAux card filter zero le
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux card filter zero le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L148-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L148-L162

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_card_filter_zero_le (D n : ℕ) :
    ((Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0)).card ≤
      (Finset.Nat.antidiagonalTuple D (n + 1)).card := by sorry
