-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_filter_zero_eq_empty
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_filter_zero_eq_empty
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:42.280936+00:00
-- url     : https://prove2.me/theorems/c9d5669d-ce36-47a5-a2d9-45f4d0957537
-- title:
--   Geometry Of Numbers Theory: chi PAux filter zero eq empty
-- statement:
--   The Geometry Of Numbers Theory construction uses the chi PAux filter zero eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L164-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/ChiPSt.lean#L164-L169

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_filter_zero_eq_empty (n : ℕ) :
    (Finset.Nat.antidiagonalTuple (0 + 1) (n + 1)).filter (fun b => b 0 = 0) = ∅ := by sorry
