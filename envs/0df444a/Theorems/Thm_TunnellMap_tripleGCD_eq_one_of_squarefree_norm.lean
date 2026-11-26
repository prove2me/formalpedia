-- Prove2me | Theorems.Thm_TunnellMap_tripleGCD_eq_one_of_squarefree_norm
-- name    : TunnellMap.tripleGCD_eq_one_of_squarefree_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:21.830648+00:00
-- url     : https://prove2.me/theorems/1af540d5-c18b-51d3-9495-964a9db91796
-- title:
--   Tunnell Map: triple GCD eq one of squarefree norm
-- statement:
--   A squarefree squared norm forces the coordinate gcd to be one.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrthogonalFrameExistence.lean#L40-L61
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrthogonalFrameExistence.lean#L40-L61

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.tripleGCD_eq_one_of_squarefree_norm {p : Triple} {n : ℤ}
    (hn : Squarefree n) (hnorm : dot p p = n) : tripleGCD p = 1 := by sorry
