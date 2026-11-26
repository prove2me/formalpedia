-- Prove2me | Theorems.Thm_TunnellMap_polynomial_content_neg
-- name    : TunnellMap.polynomial_content_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:27.78685+00:00
-- url     : https://prove2.me/theorems/60992dbe-7939-4f64-ac1b-32c481ecdf8a
-- title:
--   Tunnell Map: polynomial content neg
-- statement:
--   The Tunnell Map construction uses the polynomial content neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L109-L112
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L109-L112

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.polynomial_content_neg (f : ℤ[X]) : (-f).content = f.content := by sorry
