-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_torsion_roots
-- name    : RiemannMasullo.regulator_torsion_roots
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:12:38.089699+00:00
-- url     : https://prove2.me/theorems/3ebf7da3-e501-4928-9d9b-ce83e0a44779
-- title:
--   Torsion units as roots of unity
-- statement:
--   Torsion units are precisely the roots of unity of order dividing the cardinality of the unit torsion subgroup.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L150-L151

import Mathlib
set_option maxSynthPendingDepth 8
open scoped Classical
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
local notation "𝓤" => Additive ((𝓞 F)ˣ ⧸ Units.torsion F)

namespace RiemannMasullo

theorem regulator_torsion_roots : Units.torsion F = rootsOfUnity (Units.torsionOrder F) (𝓞 F) := by sorry

end RiemannMasullo
