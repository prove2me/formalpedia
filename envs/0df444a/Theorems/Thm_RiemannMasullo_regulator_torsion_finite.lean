-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_torsion_finite
-- name    : RiemannMasullo.regulator_torsion_finite
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:12:39.575858+00:00
-- url     : https://prove2.me/theorems/dab33272-5327-41f3-a981-f981bf29604c
-- title:
--   Finiteness of the group of torsion units
-- statement:
--   The torsion subgroup of the units in the ring of integers is finite.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L154-L155

import Mathlib
set_option maxSynthPendingDepth 8
open scoped Classical
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
local notation "𝓤" => Additive ((𝓞 F)ˣ ⧸ Units.torsion F)

namespace RiemannMasullo

theorem regulator_torsion_finite : Finite (Units.torsion F) := by sorry

end RiemannMasullo
