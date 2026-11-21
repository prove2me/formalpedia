-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_units_finitelyGenerated
-- name    : RiemannMasullo.regulator_units_finitelyGenerated
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:34:54.78061+00:00
-- url     : https://prove2.me/theorems/c1bb51b1-0476-4569-8bdc-36966e397085
-- title:
--   The integer units of a number field are finitely generated
-- statement:
--   The group of units of the ring of integers in a number field has a finite generating set.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L162-L163

import Mathlib
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]

namespace RiemannMasullo

theorem regulator_units_finitelyGenerated : Group.FG (𝓞 F)ˣ := by sorry

end RiemannMasullo
