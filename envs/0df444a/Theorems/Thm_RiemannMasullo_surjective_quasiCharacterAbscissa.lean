-- Prove2me | Theorems.Thm_RiemannMasullo_surjective_quasiCharacterAbscissa
-- name    : RiemannMasullo.surjective_quasiCharacterAbscissa
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:48:32.569187+00:00
-- url     : https://prove2.me/theorems/43dad58a-6341-4d15-98ab-6cefb02dc082
-- title:
--   Surjectivity of the quasi-character abscissa
-- statement:
--   Every real number occurs as the abscissa of a continuous quasi-character for a nontrivial proper module.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L130-L132

import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

namespace RiemannMasullo

theorem surjective_quasiCharacterAbscissa (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Surjective (quasiCharacterAbscissa m hm hne) := by sorry

end RiemannMasullo
