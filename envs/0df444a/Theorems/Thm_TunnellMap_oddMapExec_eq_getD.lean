-- Prove2me | Theorems.Thm_TunnellMap_oddMapExec_eq_getD
-- name    : TunnellMap.oddMapExec_eq_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:57:30.609011+00:00
-- url     : https://prove2.me/theorems/3ebb72a1-34a0-4632-855b-eedf33eeb7dd
-- title:
--   Tunnell Map: odd Map Exec eq get D
-- statement:
--   The Tunnell Map construction uses the odd Map Exec eq get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L276-L285
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L276-L285

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.oddMapExec_eq_getD (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (q : BOddRep n) :
    oddMapExec hnpos hsq fallback q =
      (oddMapExecOpt hnpos hsq q).getD fallback.1 := by sorry
