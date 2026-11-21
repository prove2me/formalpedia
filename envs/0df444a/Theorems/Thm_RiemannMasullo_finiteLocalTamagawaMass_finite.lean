-- Prove2me | Theorems.Thm_RiemannMasullo_finiteLocalTamagawaMass_finite
-- name    : RiemannMasullo.finiteLocalTamagawaMass_finite
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:53:01.16465+00:00
-- url     : https://prove2.me/theorems/00a34660-80dd-4ef3-8259-e8c4f806b58a
-- title:
--   The finite-place Tamagawa masses equal one almost everywhere
-- statement:
--   Only finitely many finite places have local different mass unequal to one.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec3.lean#L165-L166

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

theorem finiteLocalTamagawaMass_finite :
    {v : Primes(F) | differentMass(F, v) ≠ 1}.Finite := by sorry

end RiemannMasullo
