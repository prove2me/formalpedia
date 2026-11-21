-- Prove2me | Theorems.Thm_RiemannMasullo_quasiCharacterAbscissa_dual
-- name    : RiemannMasullo.quasiCharacterAbscissa_dual
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:48:33.947776+00:00
-- url     : https://prove2.me/theorems/8c3c94e2-b12b-470b-9a1c-6949bcd46a15
-- title:
--   Duality reflects the abscissa
-- statement:
--   The abscissa of the dual quasi-character is one minus the original abscissa.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L178-L191

import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

namespace RiemannMasullo

theorem quasiCharacterAbscissa_dual [IsTopologicalGroup G] (hm : IsProperMap m)
    (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) :
    quasiCharacterAbscissa m hm hne (dualQuasiCharacter m hm.continuous c) =
      1 - quasiCharacterAbscissa m hm hne c := by sorry

end RiemannMasullo
