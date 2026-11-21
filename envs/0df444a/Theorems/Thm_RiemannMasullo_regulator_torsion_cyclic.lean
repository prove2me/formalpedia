-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_torsion_cyclic
-- name    : RiemannMasullo.regulator_torsion_cyclic
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:12:42.560971+00:00
-- url     : https://prove2.me/theorems/3a6e0da4-2bd3-44f7-a72f-a8b3f5fd2765
-- title:
--   Cyclicity of the group of torsion units
-- statement:
--   The torsion subgroup of integer units is cyclic.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L158-L159

import Mathlib
set_option maxSynthPendingDepth 8
open scoped Classical
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
local notation "𝓤" => Additive ((𝓞 F)ˣ ⧸ Units.torsion F)

namespace RiemannMasullo

theorem regulator_torsion_cyclic : IsCyclic (Units.torsion F) := by sorry

end RiemannMasullo
