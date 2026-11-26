-- Prove2me | Theorems.Thm_TunnellMap_Examples41_lattice_scalar_data
-- name    : TunnellMap.Examples41.lattice_scalar_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:07:28.97946+00:00
-- url     : https://prove2.me/theorems/2f71256e-c9a7-4933-b5f8-c2dfa9b43066
-- title:
--   Examples41: lattice scalar data
-- statement:
--   The Examples41 construction uses the lattice scalar data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L36-L44
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L36-L44

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.lattice_scalar_data :
    alpha frame41 = 1 ∧
      beta frame41 = 0 ∧
      dot frame41.e₂ frame41.e₂ = 41 ∧
      delta frame41 = 0 ∧
      epsilon frame41 = 9 ∧
      dot frame41.z frame41.z = 2 ∧
      K frame41 = -9 := by sorry
