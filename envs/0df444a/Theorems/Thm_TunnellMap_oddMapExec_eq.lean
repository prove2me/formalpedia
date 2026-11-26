-- Prove2me | Theorems.Thm_TunnellMap_oddMapExec_eq
-- name    : TunnellMap.oddMapExec_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:25:54.266399+00:00
-- url     : https://prove2.me/theorems/4a5c9f2e-382a-52aa-8392-d8d6df299735
-- title:
--   Tunnell Map: odd Map Exec eq
-- statement:
--   **The executable odd branch agrees with the structural odd equivalence.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean#L63-L78
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableFullMap.lean#L63-L78

import Definitions.Def_TunnellMap_ComputableDirect
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_FullAssembly
import Definitions.Def_TunnellMap_ComputableFullMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.oddMapExec_eq (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbal : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (fallback : AResidual n) (q : BOddRep n) :
    oddMapExec hnpos hsq fallback q = oddEquivOfBalance hn hnpos hbal q := by sorry
