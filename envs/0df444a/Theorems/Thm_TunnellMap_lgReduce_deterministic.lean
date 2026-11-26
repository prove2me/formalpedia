-- Prove2me | Theorems.Thm_TunnellMap_lgReduce_deterministic
-- name    : TunnellMap.lgReduce_deterministic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:53:43.1909+00:00
-- url     : https://prove2.me/theorems/bc201dac-92e7-4c76-b22b-be07daf43f0b
-- title:
--   Tunnell Map: lg Reduce deterministic
-- statement:
--   **Determinism.**  The reduction is a function of the input pair alone: no
--   choice, ordering or auxiliary data enters, so any two executions on equal
--   inputs return equal outputs.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L346-L347
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L346-L347

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem TunnellMap.lgReduce_deterministic {u v u' v' : Triple} (hu : u = u') (hv : v = v') :
    lgReduce u v = lgReduce u' v' := by sorry
