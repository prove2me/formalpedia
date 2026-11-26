-- Prove2me | Theorems.Thm_TunnellMap_intIcc_sort_eq
-- name    : TunnellMap.intIcc_sort_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:34:52.681249+00:00
-- url     : https://prove2.me/theorems/b30f728f-8dac-49f3-8257-429758c3b480
-- title:
--   Tunnell Map: int Icc sort eq
-- statement:
--   The Tunnell Map construction uses the int Icc sort eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L51-L53
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L51-L53

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.intIcc_sort_eq (lo hi : ℤ) : (intIcc lo hi).sort (· ≤ ·) = intIccL lo hi := by sorry
