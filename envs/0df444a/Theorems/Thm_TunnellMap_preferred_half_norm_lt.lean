-- Prove2me | Theorems.Thm_TunnellMap_preferred_half_norm_lt
-- name    : TunnellMap.preferred_half_norm_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:04.066891+00:00
-- url     : https://prove2.me/theorems/168d9a74-9ad9-40b9-8fff-6d305ceb4f89
-- title:
--   Tunnell Map: preferred half norm lt
-- statement:
--   The Tunnell Map construction uses the preferred half norm lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GeneratorRecovery.lean#L23-L37
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GeneratorRecovery.lean#L23-L37

import Definitions.Def_TunnellMap_MidpointRecord
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_QuadraticRoots
import Definitions.Def_TunnellMap_TauLattice
import Definitions.Def_TunnellMap_GeneratorRecovery
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.preferred_half_norm_lt {n : ℤ} (hn : Odd n)
    {s : BResidual n} {t : AResidual n} (R : PreferredMidpointRecord s t) :
    R.multiplier ^ 2 * qForm R.direction < n := by sorry
