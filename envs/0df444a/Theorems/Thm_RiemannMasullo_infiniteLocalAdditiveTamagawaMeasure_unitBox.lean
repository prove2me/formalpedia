-- Prove2me | Theorems.Thm_RiemannMasullo_infiniteLocalAdditiveTamagawaMeasure_unitBox
-- name    : RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure_unitBox
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T00:53:02.119177+00:00
-- url     : https://prove2.me/theorems/f62d1e9a-ebf7-4b0a-9760-d8002e3cc9da
-- title:
--   Archimedean Tamagawa masses of the real unit interval and complex unit square
-- statement:
--   The real interval has local additive Tamagawa mass one and the complex unit square has mass two.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec3.lean#L131-L136

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

theorem infiniteLocalAdditiveTamagawaMeasure_unitBox (v : InfinitePlace F) :
    (∀ h : v.IsReal, infiniteLocalAdditiveTamagawaMeasure F v
      ((ringEquivRealOfIsReal h).symm '' Icc (0 : ℝ) 1) = 1) ∧
    (∀ h : v.IsComplex, infiniteLocalAdditiveTamagawaMeasure F v
      ((ringEquivComplexOfIsComplex h).symm '' {z : ℂ | z.re ∈ Icc 0 1 ∧ z.im ∈ Icc 0 1}) = 2) := by sorry

end RiemannMasullo
