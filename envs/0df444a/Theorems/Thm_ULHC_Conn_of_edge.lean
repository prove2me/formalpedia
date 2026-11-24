-- Prove2me | Theorems.Thm_ULHC_Conn_of_edge
-- name    : ULHC.Conn.of_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:01.399662+00:00
-- url     : https://prove2.me/theorems/1164e25b-782e-498b-8477-ba635767be68
-- title:
--   Conn: of edge
-- statement:
--   The Conn construction uses the of edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L51-L52
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L51-L52

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
set_option autoImplicit true
open ULHC

theorem ULHC.Conn.of_edge {F : Finset Edge} {e : Edge} (he : e ∈ F) : Conn F e.p e.q := by sorry
