-- Prove2me | Theorems.Thm_TunnellMap_Examples41_lattice_roots_example
-- name    : TunnellMap.Examples41.lattice_roots_example
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:08:21.935366+00:00
-- url     : https://prove2.me/theorems/442ca673-9cb9-4db8-97a6-431a463c82dc
-- title:
--   Examples41: lattice roots example
-- statement:
--   The Examples41 construction uses the lattice roots example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L66-L68
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L66-L68

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.lattice_roots_example :
    rootValues frame41 20 1 (-4) = ({2, -2} : Finset ℤ) := by sorry
