-- Prove2me | Theorems.Thm_RiemannMasullo_one_mem_relativeRightHalfPlane
-- name    : RiemannMasullo.one_mem_relativeRightHalfPlane
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:11:19.790544+00:00
-- url     : https://prove2.me/theorems/27c20522-f57a-4eeb-9014-0cb94e54387d
-- title:
--   Trivial character in a relative right half-plane
-- statement:
--   The trivial quasi-character belongs to the relative right half-plane with boundary a exactly when a is negative.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L156-L159

import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterRegions
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

namespace RiemannMasullo

theorem one_mem_relativeRightHalfPlane (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (a : ℝ) :
    1 ∈ relativeRightHalfPlane m hm hne a ↔ a < 0 := by sorry

end RiemannMasullo
