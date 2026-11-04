-- Prove2me | Theorems.Thm_ThreeSum_LocalGraph_equalityMask_eq_iff_union_eq
-- name    : ThreeSum.LocalGraph.equalityMask_eq_iff_union_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:07:06.522198+00:00
-- url     : https://prove2.me/theorems/40320ca6-60b5-4169-b198-0d6b320de5f6
-- title:
--   Local Graph: equality Mask eq iff union eq
-- statement:
--   The Local Graph construction uses the equality Mask eq iff union eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L70-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalGraph.lean#L70-L75

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LocalGraph
set_option autoImplicit false
open ThreeSum ThreeSum.LocalGraph
variable {α : Type*} [DecidableEq α]

theorem ThreeSum.LocalGraph.equalityMask_eq_iff_union_eq {s v s' v' : Finset α}
    (hd : Disjoint s v) (hd' : Disjoint s' v') :
    (fun i => leftWord s i == rightWord v i) =
        (fun i => leftWord s' i == rightWord v' i) ↔ s ∪ v = s' ∪ v' := by sorry
