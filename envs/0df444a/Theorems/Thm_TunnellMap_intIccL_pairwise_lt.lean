-- Prove2me | Theorems.Thm_TunnellMap_intIccL_pairwise_lt
-- name    : TunnellMap.intIccL_pairwise_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:30:50.543809+00:00
-- url     : https://prove2.me/theorems/3c2b58e1-984a-433e-bd75-89e121315bfe
-- title:
--   Tunnell Map: int Icc L pairwise lt
-- statement:
--   The Tunnell Map construction uses the int Icc L pairwise lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L42-L49
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L42-L49

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.intIccL_pairwise_lt (lo hi : ℤ) : (intIccL lo hi).Pairwise (· < ·) := by sorry
