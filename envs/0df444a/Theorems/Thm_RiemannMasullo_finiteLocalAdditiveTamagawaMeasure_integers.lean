-- Prove2me | Theorems.Thm_RiemannMasullo_finiteLocalAdditiveTamagawaMeasure_integers
-- name    : RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_integers
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:53:07.998473+00:00
-- url     : https://prove2.me/theorems/b415dbd4-ebf3-4456-b82e-b05bb77f304c
-- title:
--   Tamagawa mass of the finite local integer ring
-- statement:
--   At a finite place the additive Tamagawa mass of the integer ring equals the inverse square root of the local different norm.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec3.lean#L154-L156

import Mathlib
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Definitions.Def_RiemannMasullo_LocalAdditiveTamagawaMeasures
open RiemannMasullo
open Function MeasureTheory NumberField IsDedekindDomain InfinitePlace.Completion Set
open scoped Classical ENNReal NNReal NumberField.AdeleRing Pointwise

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
noncomputable local instance (v : InfinitePlace F) : MeasurableSpace v.Completion := borel _
noncomputable local instance (v : Primes(F)) : MeasurableSpace (v.adicCompletion F) := borel _
noncomputable local instance (v : Primes(F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
noncomputable local instance (v : Primes(F)) : LocallyCompactSpace (v.adicCompletion F) :=
  RiemannMasullo.locallyCompactSpace_adicCompletion v
local notation "differentExp(" F ", " v ")" =>
  multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))
local notation "differentMass(" F ", " v ")" =>
  Inv.inv (ENNReal.ofReal (Real.sqrt (Nat.cast (Ideal.absNorm (HeightOneSpectrum.asIdeal v)) ^
    differentExp(F, v))))

namespace RiemannMasullo

theorem finiteLocalAdditiveTamagawaMeasure_integers (v : Primes(F)) :
    finiteLocalAdditiveTamagawaMeasure F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      differentMass(F, v) := by sorry

end RiemannMasullo
