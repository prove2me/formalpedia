-- Prove2me | Theorems.Thm_ULHC_card_cand_le
-- name    : ULHC.card_cand_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:38:31.188853+00:00
-- url     : https://prove2.me/theorems/9384c393-2205-4bcc-852b-027bd93e2fbc
-- title:
--   ULHC: card cand le
-- statement:
--   The ULHC construction uses the card cand le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L53-L60
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AlgComplete.lean#L53-L60

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}

theorem ULHC.card_cand_le (G : Finset Edge) :
    (cand V G).card ≤ 4 * V.card + V.card * (4 * V.card) := by sorry
