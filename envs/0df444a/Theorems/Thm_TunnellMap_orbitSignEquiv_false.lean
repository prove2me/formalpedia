-- Prove2me | Theorems.Thm_TunnellMap_orbitSignEquiv_false
-- name    : TunnellMap.orbitSignEquiv_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:47:11.507065+00:00
-- url     : https://prove2.me/theorems/8d87d36c-a679-44d2-92f6-18f2979268a3
-- title:
--   Tunnell Map: orbit Sign Equiv false
-- statement:
--   The Tunnell Map construction uses the orbit Sign Equiv false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitLift.lean#L79-L98
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitLift.lean#L79-L98

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_Assembly
import Definitions.Def_TunnellMap_OrbitLift
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.orbitSignEquiv_false {n : ℤ} (hnpos : 0 < n)
    (s : (bResidualInvolution n).Orbit)
    (t : (aResidualInvolution n hnpos).Orbit) :
    orbitSignEquiv hnpos s t false =
      if directionKey
          (plusVector ((bResidualInvolution n).representative s)
            ((aResidualInvolution n hnpos).representative t)) <
          directionKey
          (minusVector ((bResidualInvolution n).representative s)
            ((aResidualInvolution n hnpos).representative t)) then
        false
      else
        true := by sorry
