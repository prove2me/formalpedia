-- Prove2me | Theorems.Thm_ULHC_chain_len
-- name    : ULHC.chain_len
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:12:24.165796+00:00
-- url     : https://prove2.me/theorems/95658cd1-8c83-4113-8760-db69c82cebb2
-- title:
--   ULHC: chain len
-- statement:
--   The ULHC construction uses the chain len property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostAlg.lean#L108-L115
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostAlg.lean#L108-L115

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostAlg
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.chain_len {V : Finset Pt} {G : Finset Edge} :
    ∀ (L : List StripSpec) (σ : StripSpec), CRChain V G σ L → L.length ≤ (L.map StripSpec.n).sum
  := by sorry
