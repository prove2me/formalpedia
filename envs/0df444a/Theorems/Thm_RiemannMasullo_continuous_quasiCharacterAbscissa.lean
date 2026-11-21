-- Prove2me | Theorems.Thm_RiemannMasullo_continuous_quasiCharacterAbscissa
-- name    : RiemannMasullo.continuous_quasiCharacterAbscissa
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:48:32.321184+00:00
-- url     : https://prove2.me/theorems/f2e22d28-9cbc-4a6a-9d61-32ac012d98ad
-- title:
--   Continuity of the quasi-character abscissa
-- statement:
--   The abscissa is a continuous function on the space of quasi-characters.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L122-L127

import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

namespace RiemannMasullo

theorem continuous_quasiCharacterAbscissa (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Continuous (quasiCharacterAbscissa m hm hne) := by sorry

end RiemannMasullo
