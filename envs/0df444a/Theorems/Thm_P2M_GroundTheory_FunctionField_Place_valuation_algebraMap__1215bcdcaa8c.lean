-- Prove2me | Theorems.Thm_P2M_GroundTheory_FunctionField_Place_valuation_algebraMap__1215bcdcaa8c
-- name    : P2M_GroundTheory_FunctionField_Place_valuation_algebraMap__1215bcdcaa8c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:48.712289+00:00
-- url     : https://prove2.me/theorems/9895c706-cce2-47d6-b06c-0cb48c1e22d0
-- title:
--   P2 M Ground Theory Function Field Place valuation algebra Map  1215bcdcaa8c: P2 M Ground Theory Function Field Place valuation algebra Map  1215bcdcaa8c
-- statement:
--   The P2 M Ground Theory Function Field Place valuation algebra Map  1215bcdcaa8c construction uses the P2 M Ground Theory Function Field Place valuation algebra Map  1215bcdcaa8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L404-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L404-L405

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IntermediateField
open scoped WithZero
open Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
open GroundTheory.FunctionField.Place
variable {k K} (v : Place k K)
variable [IsFunctionField k K]

theorem P2M_GroundTheory_FunctionField_Place_valuation_algebraMap__1215bcdcaa8c {c : k} (hc : c ≠ 0) : v.valuation (algebraMap k K c) = 1 := by sorry

alias «GroundTheory».«FunctionField».«Place».«valuation_algebraMap'» := P2M_GroundTheory_FunctionField_Place_valuation_algebraMap__1215bcdcaa8c
