-- Prove2me | Theorems.Thm_ULHC_progress_step_CA
-- name    : ULHC.progress_step_CA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:36:27.999364+00:00
-- url     : https://prove2.me/theorems/db6f1667-4c7d-4b60-9f96-49dcb7a3102b
-- title:
--   ULHC: progress step CA
-- statement:
--   The ULHC construction uses the progress step CA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L379-L385
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L379-L385

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
  {a : StripSpec} (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
  (hT' : NoTypeIII V (applyS G a))
include hG hT ha hae ha2 hT'

theorem ULHC.progress_step_CA {b : StripSpec} {L : List StripSpec} (hch : CRChain V G a (b :: L))
    (hcat : CATail (a :: b :: L)) (hfar : FarChainCA G a b L) :
    CRPathCA V (applyS G a) b L ∧ wt b L + a.n = wt a (b :: L) := by sorry
