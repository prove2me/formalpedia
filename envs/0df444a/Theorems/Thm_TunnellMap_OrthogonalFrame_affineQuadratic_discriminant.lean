-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_affineQuadratic_discriminant
-- name    : TunnellMap.OrthogonalFrame.affineQuadratic_discriminant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:35.979445+00:00
-- url     : https://prove2.me/theorems/367fc87f-a54c-5a4d-b03e-05345aa6be9b
-- title:
--   Orthogonal Frame: affine Quadratic discriminant
-- statement:
--   The Orthogonal Frame construction uses the affine Quadratic discriminant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L89-L100
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L89-L100

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.affineQuadratic_discriminant (A q b : ℤ) :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let γ := dot F.e₂ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let ζ := dot F.z F.z
    let t := q * A
    quadraticHalfDiscriminant α (β * b + t * δ)
      (γ * b ^ 2 + 2 * t * ε * b + t ^ 2 * ζ - A) =
        F.halfDiscriminant A q b := by sorry
