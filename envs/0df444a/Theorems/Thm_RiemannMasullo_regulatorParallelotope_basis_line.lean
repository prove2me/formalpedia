-- Prove2me | Theorems.Thm_RiemannMasullo_regulatorParallelotope_basis_line
-- name    : RiemannMasullo.regulatorParallelotope_basis_line
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:12:31.621718+00:00
-- url     : https://prove2.me/theorems/a14a25e9-3747-4834-b8fb-a8c7a7a3d0ce
-- title:
--   The half-open interval along each regulator basis vector
-- statement:
--   A multiple of a chosen regulator basis vector belongs to the fundamental parallelotope exactly when its coefficient belongs to [0,1).
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L186-L188

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

theorem regulatorParallelotope_basis_line (i : Fin (Units.rank F)) (t : ℝ) :
    t • Units.logEmbeddingQuot F (b i) ∈ regulatorParallelotope F b ↔ t ∈ Set.Ico 0 1 := by sorry

end RiemannMasullo
