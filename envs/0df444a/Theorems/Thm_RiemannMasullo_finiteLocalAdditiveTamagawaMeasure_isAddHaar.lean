-- Prove2me | Theorems.Thm_RiemannMasullo_finiteLocalAdditiveTamagawaMeasure_isAddHaar
-- name    : RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_isAddHaar
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:53:03.270993+00:00
-- url     : https://prove2.me/theorems/920902ba-7d8c-4b24-9b8a-02fb6418ead8
-- title:
--   The finite local Tamagawa measure is additive Haar
-- statement:
--   The locally normalized additive Tamagawa measure at each finite place is an additive Haar measure.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec3.lean#L160-L161

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

theorem finiteLocalAdditiveTamagawaMeasure_isAddHaar (v : Primes(F)) :
    (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := by sorry

end RiemannMasullo
