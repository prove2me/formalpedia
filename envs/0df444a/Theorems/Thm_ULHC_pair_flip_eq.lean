-- Prove2me | Theorems.Thm_ULHC_pair_flip_eq
-- name    : ULHC.pair_flip_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:40:07.037798+00:00
-- url     : https://prove2.me/theorems/fd5cb343-6b53-44a5-8d5e-bda267bb6b73
-- title:
--   ULHC: pair flip eq
-- statement:
--   The ULHC construction uses the pair flip eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L251-L257
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L251-L257

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.pair_flip_eq {F : Finset Edge} (c : Pt) (s : Side)
    (h1 : lat1 c s ∈ F) (h2 : lat2 c s ∈ F) (h3 : front (nb c s) s ∈ F)
    (h4 : back c s ∉ F) (h5 : lat1 (nb c s) s ∉ F) (h6 : lat2 (nb c s) s ∉ F) :
    flip (flip F (nb c s)) c = (mkPair c s).res F := by sorry
