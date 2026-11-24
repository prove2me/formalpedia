-- Prove2me | Theorems.Thm_ULHC_T_pickSrcT_ret
-- name    : ULHC.T.pickSrcT_ret
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:14:58.276782+00:00
-- url     : https://prove2.me/theorems/269c8d05-c013-4ae3-955c-cbd6f02cdc2f
-- title:
--   T: pick Src T ret
-- statement:
--   The T construction uses the pick Src T ret property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L136-L138
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L136-L138

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.pickSrcT_ret (srcT : α → TimeM Bool) (tbl : List (α × Option (ℕ × List α))) :
    (pickSrcT NL srcT tbl).ret = MP.pickSrc NL (fun x => (srcT x).ret) tbl := by sorry
