-- Prove2me | Theorems.Thm_RiemannMasullo_regulatorParallelotope_precompact
-- name    : RiemannMasullo.regulatorParallelotope_precompact
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:12:31.88239+00:00
-- url     : https://prove2.me/theorems/eb8043de-21be-442f-889c-cdb51bd954d5
-- title:
--   Compact closure of the regulator parallelotope
-- statement:
--   The closure of the regulator parallelotope is compact.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L196-L197

import Mathlib
import Definitions.Def_RiemannMasullo_RegulatorParallelotope
set_option maxSynthPendingDepth 8
open scoped Classical
open RiemannMasullo
open scoped Pointwise
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

namespace RiemannMasullo

theorem regulatorParallelotope_precompact : IsCompact (closure (regulatorParallelotope F b)) := by sorry

end RiemannMasullo
