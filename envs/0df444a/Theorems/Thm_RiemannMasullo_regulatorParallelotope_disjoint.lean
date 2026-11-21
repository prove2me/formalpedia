-- Prove2me | Theorems.Thm_RiemannMasullo_regulatorParallelotope_disjoint
-- name    : RiemannMasullo.regulatorParallelotope_disjoint
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:12:33.957965+00:00
-- url     : https://prove2.me/theorems/ccf65c52-e348-4130-a1e9-a2453a1fd363
-- title:
--   Nonzero regulator translates are disjoint
-- statement:
--   A nonzero translation by a unit logarithm takes the half-open regulator parallelotope to a disjoint set.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L209-L211

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

theorem regulatorParallelotope_disjoint (x : (Units.logEmbedding F).range) (hx : x ≠ 0) :
    Disjoint (x.val +ᵥ regulatorParallelotope F b) (regulatorParallelotope F b) := by sorry

end RiemannMasullo
