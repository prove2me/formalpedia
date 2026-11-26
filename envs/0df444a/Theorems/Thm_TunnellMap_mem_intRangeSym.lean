-- Prove2me | Theorems.Thm_TunnellMap_mem_intRangeSym
-- name    : TunnellMap.mem_intRangeSym
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:05:30.591529+00:00
-- url     : https://prove2.me/theorems/53019d99-69a6-585b-bbf0-88caaadead92
-- title:
--   Tunnell Map: mem int Range Sym
-- statement:
--   The Tunnell Map construction uses the mem int Range Sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L50-L57
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L50-L57

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_intRangeSym {m a : ℤ} (h₁ : -m ≤ a) (h₂ : a ≤ m) : a ∈ intRangeSym m := by sorry
