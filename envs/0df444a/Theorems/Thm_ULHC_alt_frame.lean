-- Prove2me | Theorems.Thm_ULHC_alt_frame
-- name    : ULHC.alt_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:01:18.212162+00:00
-- url     : https://prove2.me/theorems/58d698b2-fe93-4018-ab8e-f81373905abc
-- title:
--   ULHC: alt frame
-- statement:
--   The ULHC construction uses the alt frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L101-L115
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L101-L115

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.alt_frame {F : Finset Edge} {w : Pt} {tw : Side} (s : Side)
    (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F) :
    (back w s ∈ F ↔ front w s ∈ F) ∧ (lat1 w s ∈ F ↔ lat2 w s ∈ F) ∧
      (back w s ∈ F ↔ lat1 w s ∉ F) := by sorry
