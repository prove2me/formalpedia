-- Prove2me | Theorems.Thm_TunnellMap_mem_intIccL
-- name    : TunnellMap.mem_intIccL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:30:20.773839+00:00
-- url     : https://prove2.me/theorems/a86ce5c7-a9c6-4535-9a4e-7c2161d0aa44
-- title:
--   Tunnell Map: mem int Icc L
-- statement:
--   The Tunnell Map construction uses the mem int Icc L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L29-L40
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L29-L40

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.mem_intIccL {lo hi x : ℤ} : x ∈ intIccL lo hi ↔ lo ≤ x ∧ x ≤ hi := by sorry
