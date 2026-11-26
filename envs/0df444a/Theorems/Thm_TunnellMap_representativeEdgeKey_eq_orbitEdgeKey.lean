-- Prove2me | Theorems.Thm_TunnellMap_representativeEdgeKey_eq_orbitEdgeKey
-- name    : TunnellMap.representativeEdgeKey_eq_orbitEdgeKey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:51.11062+00:00
-- url     : https://prove2.me/theorems/9d18491c-81fb-4bfe-bc00-1451d3544f19
-- title:
--   Tunnell Map: representative Edge Key eq orbit Edge Key
-- statement:
--   Computing the orbit key from any signed representatives gives the same
--   answer.  This is the representative-independence assertion in Lemma 4.1.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitRanking.lean#L72-L101
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitRanking.lean#L72-L101

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_OrbitRanking
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.representativeEdgeKey_eq_orbitEdgeKey {n : ℤ} (hnpos : 0 < n)
    (s : BResidual n) (t : AResidual n) :
    representativeEdgeKey s t =
      orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((aResidualInvolution n hnpos).orbit t) := by sorry
