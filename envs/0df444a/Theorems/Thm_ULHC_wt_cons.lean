-- Prove2me | Theorems.Thm_ULHC_wt_cons
-- name    : ULHC.wt_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:01:24.620152+00:00
-- url     : https://prove2.me/theorems/5def5b00-f311-490b-be5c-340920fc95a7
-- title:
--   ULHC: wt cons
-- statement:
--   The ULHC construction uses the wt cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L183-L184
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L183-L184

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.wt_cons (τ w : StripSpec) (L : List StripSpec) : wt τ (w :: L) = τ.n + wt w L := by sorry
