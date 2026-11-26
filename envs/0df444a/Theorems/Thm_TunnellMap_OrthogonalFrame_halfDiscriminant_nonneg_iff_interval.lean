-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_halfDiscriminant_nonneg_iff_interval
-- name    : TunnellMap.OrthogonalFrame.halfDiscriminant_nonneg_iff_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:51.051005+00:00
-- url     : https://prove2.me/theorems/d0e78dcd-a65b-4fb3-8172-86104f62c12d
-- title:
--   Orthogonal Frame: half Discriminant nonneg iff interval
-- statement:
--   The exact floor/ceiling form of the finite `b`-interval in Lemma 5.3.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ShortInterval.lean#L84-L109
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ShortInterval.lean#L84-L109

import Definitions.Def_TunnellMap_AffineLattice
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Rat.Floor
import Definitions.Def_TunnellMap_ShortInterval
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.halfDiscriminant_nonneg_iff_interval
    {n A q b : ℤ} (hn : 0 < n) (hpNorm : dot p p = n)
    (hAM :
      0 ≤ dot F.e₁ F.e₁ * (A * (n - q ^ 2 * A))) :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let t := q * A
    let K := β * δ - α * ε
    let M := A * (n - q ^ 2 * A)
    0 ≤ F.halfDiscriminant A q b ↔
      ⌈((t * K - Int.sqrt (α * M) : ℤ) : ℚ) / (n : ℚ)⌉ ≤ b ∧
        b ≤ ⌊((t * K + Int.sqrt (α * M) : ℤ) : ℚ) / (n : ℚ)⌋ := by sorry
