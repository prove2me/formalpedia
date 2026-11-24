-- Prove2me | Theorems.Thm_ULHC_chainOK_besideA
-- name    : ULHC.chainOK_besideA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:01:02.396588+00:00
-- url     : https://prove2.me/theorems/64dbc5a7-397f-4456-835c-b56f4b89a92a
-- title:
--   ULHC: chain OK beside A
-- statement:
--   The ULHC construction uses the chain OK beside A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L74-L82
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L74-L82

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.chainOK_besideA (c : Pt) (s : Side) (k : ℕ) :
    ChainOK ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latA s), s, 1⟩ := by sorry
