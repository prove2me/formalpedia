-- Prove2me | Theorems.Thm_ULHC_link_transfer_CA
-- name    : ULHC.link_transfer_CA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:57:55.528888+00:00
-- url     : https://prove2.me/theorems/d735c324-199b-45c5-8135-4afe6c312958
-- title:
--   ULHC: link transfer CA
-- statement:
--   The ULHC construction uses the link transfer CA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L259-L365
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L259-L365

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
  {a : StripSpec} (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
  (hT' : NoTypeIII V (applyS G a))
include hG hT ha hae ha2 hT'

theorem ULHC.link_transfer_CA {σ τ : StripSpec} (hσ : EndOK V G σ) (hev : σ.n % 2 = 0)
    (hl : CR2 V G σ τ) (hok : ChainOK σ τ) (hfl : FarLinkCA G a σ τ) :
    CR2 V (applyS G a) σ τ := by sorry
