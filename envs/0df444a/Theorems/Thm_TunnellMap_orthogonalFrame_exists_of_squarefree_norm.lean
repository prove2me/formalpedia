-- Prove2me | Theorems.Thm_TunnellMap_orthogonalFrame_exists_of_squarefree_norm
-- name    : TunnellMap.orthogonalFrame_exists_of_squarefree_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:33.081745+00:00
-- url     : https://prove2.me/theorems/196df81f-509c-5f33-bca8-53c457a67907
-- title:
--   Tunnell Map: orthogonal Frame exists of squarefree norm
-- statement:
--   Lemma 5.1: a squarefree norm admits an oriented kernel basis and Bezout
--   vector.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrthogonalFrameExistence.lean#L117-L121
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrthogonalFrameExistence.lean#L117-L121

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.orthogonalFrame_exists_of_squarefree_norm {p : Triple} {n : ℤ}
    (hn : Squarefree n) (hnorm : dot p p = n) :
    Nonempty (OrthogonalFrame p) := by sorry
