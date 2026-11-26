-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_gram_cubic_identity
-- name    : TunnellMap.OrthogonalFrame.gram_cubic_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:57.411821+00:00
-- url     : https://prove2.me/theorems/79851860-0ff4-5743-b33a-7e6e11ed170d
-- title:
--   Orthogonal Frame: gram cubic identity
-- statement:
--   The Orthogonal Frame construction uses the gram cubic identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L181-L191
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L181-L191

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.gram_cubic_identity :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let γ := dot F.e₂ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let ζ := dot F.z F.z
    α * γ * ζ + 2 * β * δ * ε - α * ε ^ 2 - γ * δ ^ 2 - β ^ 2 * ζ = 1 := by sorry
