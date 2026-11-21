-- Prove2me | Theorems.Thm_RiemannMasullo_regulatorParallelotope_interior
-- name    : RiemannMasullo.regulatorParallelotope_interior
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:12:27.533286+00:00
-- url     : https://prove2.me/theorems/d6198f4c-4618-4240-a78e-6337b3fd6981
-- title:
--   Nonempty interior of the regulator parallelotope
-- statement:
--   The regulator parallelotope has nonempty interior in logarithmic space.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L200-L201

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

theorem regulatorParallelotope_interior : (interior (regulatorParallelotope F b)).Nonempty := by sorry

end RiemannMasullo
