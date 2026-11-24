-- Prove2me | Theorems.Thm_ULHC_chain_transfer_CA
-- name    : ULHC.chain_transfer_CA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:36:19.132412+00:00
-- url     : https://prove2.me/theorems/78924f5f-a4d1-4ddf-a716-c3e109e2ba50
-- title:
--   ULHC: chain transfer CA
-- statement:
--   The ULHC construction uses the chain transfer CA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L367-L377
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L367-L377

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
  {a : StripSpec} (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
  (hT' : NoTypeIII V (applyS G a))
include hG hT ha hae ha2 hT'

theorem ULHC.chain_transfer_CA : ∀ (L : List StripSpec) (σ : StripSpec),
    EndOK V G σ → CRChain V G σ L → CATail (σ :: L) → FarChainCA G a σ L →
      CRChain V (applyS G a) σ L := by sorry
