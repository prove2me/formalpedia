-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_units_mod_torsion_basis
-- name    : RiemannMasullo.regulator_units_mod_torsion_basis
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:12:41.254189+00:00
-- url     : https://prove2.me/theorems/64894e44-674d-4231-906d-d5afb6237e53
-- title:
--   Dirichlet basis of the units modulo torsion
-- statement:
--   The units modulo torsion admit an integral basis indexed by the number of infinite places minus one.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L167-L168

import Mathlib
set_option maxSynthPendingDepth 8
open scoped Classical
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
local notation "𝓤" => Additive ((𝓞 F)ˣ ⧸ Units.torsion F)

namespace RiemannMasullo

theorem regulator_units_mod_torsion_basis : Nonempty (Module.Basis (Fin (Units.rank F)) ℤ 𝓤) := by sorry

end RiemannMasullo
