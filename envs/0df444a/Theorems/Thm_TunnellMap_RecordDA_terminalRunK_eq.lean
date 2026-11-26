-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_terminalRunK_eq
-- name    : TunnellMap.RecordDA.terminalRunK_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:16:05.384698+00:00
-- url     : https://prove2.me/theorems/9dc302c1-84f8-4fdf-9fd1-1963408ed698
-- title:
--   Record DA: terminal Run K eq
-- statement:
--   The Record DA construction uses the terminal Run K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelFullMap.lean#L29-L33
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelFullMap.lean#L29-L33

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_KernelFullMap
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.terminalRunK_eq (hn : 0 ≤ n) (hsq : Squarefree n) (fuel : ℕ)
    (hfuel : FuelSuffices hsq fuel) :
    terminalRunK hsq fuel = terminalRunExec (framesExec hsq) := by sorry
