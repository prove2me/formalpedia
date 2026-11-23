-- Prove2me | Theorems.Thm_P2M_GroundTheory_FunctionField_Place_LiesOver_ramificationIdx__eq_69b785bc37b8
-- name    : P2M_GroundTheory_FunctionField_Place_LiesOver_ramificationIdx__eq_69b785bc37b8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:41.904464+00:00
-- url     : https://prove2.me/theorems/568a39b1-46c9-48cb-8def-9046791b7357
-- title:
--   P2 M Ground Theory Function Field Place Lies Over ramification Idx  eq 69b785bc37b8: P2 M Ground Theory Function Field Place Lies Over ramification Idx  eq 69b785bc37b8
-- statement:
--   The P2 M Ground Theory Function Field Place Lies Over ramification Idx  eq 69b785bc37b8 construction uses the P2 M Ground Theory Function Field Place Lies Over ramification Idx  eq 69b785bc37b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L188-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L188-L198

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
variable [IsFunctionField k K]
variable [IsFunctionField k K']

theorem P2M_GroundTheory_FunctionField_Place_LiesOver_ramificationIdx__eq_69b785bc37b8 {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    (IsLocalRing.maximalIdeal v.ring).ramificationIdx' (IsLocalRing.maximalIdeal w.ring) =
      w.ramificationIdx v := by sorry

alias «GroundTheory».«FunctionField».«Place».«LiesOver».«ramificationIdx'_eq» := P2M_GroundTheory_FunctionField_Place_LiesOver_ramificationIdx__eq_69b785bc37b8
