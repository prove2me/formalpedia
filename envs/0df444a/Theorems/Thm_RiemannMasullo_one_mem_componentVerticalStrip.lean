-- Prove2me | Theorems.Thm_RiemannMasullo_one_mem_componentVerticalStrip
-- name    : RiemannMasullo.one_mem_componentVerticalStrip
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:11:05.836984+00:00
-- url     : https://prove2.me/theorems/a91ec026-0408-4882-8cfb-1775e762483d
-- title:
--   Trivial character in a component vertical strip
-- statement:
--   The trivial character belongs to the strip of the trivial component over I exactly when I contains zero.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L163-L165

import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterRegions
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

namespace RiemannMasullo

theorem one_mem_componentVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (I : Set ℝ) :
    1 ∈ componentVerticalStrip m hm hne 1 I ↔ 0 ∈ I := by sorry

end RiemannMasullo
