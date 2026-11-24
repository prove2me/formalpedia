-- Prove2me | Theorems.Thm_ULHC_conn_erase_of_even
-- name    : ULHC.conn_erase_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:24.664268+00:00
-- url     : https://prove2.me/theorems/d9b184f3-d974-4905-b79c-09151afe3d5e
-- title:
--   ULHC: conn erase of even
-- statement:
--   The ULHC construction uses the conn erase of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L321-L356
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L321-L356

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.conn_erase_of_even {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) {e : Edge}
    (he : e ∈ F) (heven : ∀ z ∈ V, Conn F e.p z → Even (deg F z)) :
    Conn (F.erase e) e.p e.q := by sorry
