-- Prove2me | Theorems.Thm_TunnellMap_lgSwap_reduced
-- name    : TunnellMap.lgSwap_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:00:58.893724+00:00
-- url     : https://prove2.me/theorems/b9873963-22df-4b3c-973a-03443d2a051e
-- title:
--   Tunnell Map: lg Swap reduced
-- statement:
--   When the two vectors of a reduced pair have equal norm, the oriented swap
--   is again a reduced pair.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L260-L269
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L260-L269

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.lgSwap_reduced {uv : Triple × Triple} (h : IsReducedPair uv)
    (heq : dot uv.1 uv.1 = dot uv.2 uv.2) : IsReducedPair (lgSwap uv) := by sorry
