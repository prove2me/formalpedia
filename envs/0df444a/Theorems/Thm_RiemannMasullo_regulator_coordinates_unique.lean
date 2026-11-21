-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_coordinates_unique
-- name    : RiemannMasullo.regulator_coordinates_unique
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:16:13.076027+00:00
-- url     : https://prove2.me/theorems/c7488519-5659-4c47-8d01-471ac531fa32
-- title:
--   Unique real regulator coordinates of a norm-one archimedean idele
-- statement:
--   With any integral basis of units modulo torsion, every norm-one archimedean idele has a unique tuple of real regulator coordinates at the nondistinguished infinite places.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L174-L177

import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

open NumberField.Units.dirichletUnitTheorem
set_option maxSynthPendingDepth 8
variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

namespace RiemannMasullo

theorem regulator_coordinates_unique (g : N∞) :
    ∃! t : Fin (Units.rank F) → ℝ, ∀ w : {w : InfinitePlace F // w ≠ w₀},
      infiniteIdeleLog F g.val w.val = ∑ i, t i * Units.logEmbeddingQuot F (b i) w := by sorry

end RiemannMasullo
