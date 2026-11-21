-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_eq_infiniteIdeleLog
-- name    : RiemannMasullo.regulator_eq_infiniteIdeleLog
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:32:26.137831+00:00
-- url     : https://prove2.me/theorems/68003255-a785-4a5e-ae3b-63e5bc99e471
-- title:
--   The unit regulator is the restriction of the archimedean logarithm
-- statement:
--   At each nondistinguished infinite place the regulator of an integral unit equals the full logarithm of its diagonal archimedean idele.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L127-L129

import Mathlib
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)
open NumberField.Units.dirichletUnitTheorem
local notation "unitAtInfinity" => Units.map (RingHom.toMonoidHom
  (RingHom.comp (algebraMap F (InfiniteAdeleRing F)) (algebraMap (𝓞 F) F)))

namespace RiemannMasullo

theorem regulator_eq_infiniteIdeleLog (u : (𝓞 F)ˣ) (v : {w : InfinitePlace F // w ≠ w₀}) :
    Units.logEmbedding F (Additive.ofMul u) v = infiniteIdeleLog F (unitAtInfinity u) v.val := by sorry

end RiemannMasullo
