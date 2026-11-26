-- Prove2me | Theorems.Thm_TunnellMap_dot_vsub_vsmul
-- name    : TunnellMap.dot_vsub_vsmul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:57:33.92591+00:00
-- url     : https://prove2.me/theorems/40eb211c-5b4a-5e75-9a4d-a6e12458b9ea
-- title:
--   Tunnell Map: dot vsub vsmul
-- statement:
--   The Tunnell Map construction uses the dot vsub vsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L68-L70
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L68-L70

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.dot_vsub_vsmul (u v : Triple) (q : ℤ) :
    dot u (vsub v (vsmul q u)) = dot u v - q * dot u u := by sorry
