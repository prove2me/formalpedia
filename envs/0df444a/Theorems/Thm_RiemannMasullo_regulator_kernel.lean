-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_kernel
-- name    : RiemannMasullo.regulator_kernel
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:12:37.17287+00:00
-- url     : https://prove2.me/theorems/70c7c335-3be5-47c8-ba9f-65faf09b8051
-- title:
--   The kernel of the regulator
-- statement:
--   The kernel of the logarithmic map on integer units is the torsion subgroup.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L145-L146

import Mathlib
set_option maxSynthPendingDepth 8
open scoped Classical
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
local notation "𝓤" => Additive ((𝓞 F)ˣ ⧸ Units.torsion F)

namespace RiemannMasullo

theorem regulator_kernel : (Units.logEmbedding F).ker = (Units.torsion F).toAddSubgroup := by sorry

end RiemannMasullo
