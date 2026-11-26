-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_short_identity_aux
-- name    : TunnellMap.OrthogonalFrame.short_identity_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:52.645623+00:00
-- url     : https://prove2.me/theorems/d97693a2-a98a-5e0e-9a08-6fbd21e8cc30
-- title:
--   Orthogonal Frame: short identity aux
-- statement:
--   The Orthogonal Frame construction uses the short identity aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L193-L218
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L193-L218

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.short_identity_aux :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let ζ := dot F.z F.z
    let n := dot p p
    let K := β * δ - α * ε
    K ^ 2 + n * (δ ^ 2 - α * ζ) = -α := by sorry
