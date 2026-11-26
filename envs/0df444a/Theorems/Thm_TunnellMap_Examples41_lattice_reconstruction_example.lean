-- Prove2me | Theorems.Thm_TunnellMap_Examples41_lattice_reconstruction_example
-- name    : TunnellMap.Examples41.lattice_reconstruction_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:11:49.006412+00:00
-- url     : https://prove2.me/theorems/0b6a3d11-f965-4def-b9b6-0e33bbddb059
-- title:
--   Examples41: lattice reconstruction example
-- statement:
--   The Examples41 construction uses the lattice reconstruction example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L72-L79
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L72-L79

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.lattice_reconstruction_example :
    aValue frame41 latticeIndex = 2 ∧
      rValue frame41 latticeIndex = ⟨2, -4, 0⟩ ∧
      dValue frame41 latticeIndex = ⟨1, -4, 1⟩ ∧
      targetValue s2 frame41 latticeIndex = ⟨4, -3, 0⟩ := by sorry
