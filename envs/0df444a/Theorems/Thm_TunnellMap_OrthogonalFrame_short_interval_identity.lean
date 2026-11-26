-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_short_interval_identity
-- name    : TunnellMap.OrthogonalFrame.short_interval_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:19.552843+00:00
-- url     : https://prove2.me/theorems/a2d537a5-6438-4cc6-ac80-e67417eba283
-- title:
--   Orthogonal Frame: short interval identity
-- statement:
--   Equation (5.7) in the manuscript: `n D_b = α M - (n b - t K)^2`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ShortInterval.lean#L65-L81
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ShortInterval.lean#L65-L81

import Definitions.Def_TunnellMap_AffineLattice
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Rat.Floor
import Definitions.Def_TunnellMap_ShortInterval
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.short_interval_identity (A q b : ℤ) :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let n := dot p p
    let t := q * A
    let K := β * δ - α * ε
    let M := A * (n - q ^ 2 * A)
    n * F.halfDiscriminant A q b = α * M - (n * b - t * K) ^ 2 := by sorry
