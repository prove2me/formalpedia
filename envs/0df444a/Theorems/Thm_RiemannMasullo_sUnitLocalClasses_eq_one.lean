-- Prove2me | Theorems.Thm_RiemannMasullo_sUnitLocalClasses_eq_one
-- name    : RiemannMasullo.sUnitLocalClasses_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T01:55:52.191176+00:00
-- url     : https://prove2.me/theorems/32301dd3-9f44-4ee5-9471-31ea4fad23d5
-- title:
--   Riemann Masullo: s Unit Local Classes eq one
-- statement:
--   Paper: Equation (A.1.5.9), p. 544. A T-unit has trivial classes at the places of
--   T outside S precisely when it is already an S-unit.
--
--   Source: https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L2192-L2216
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L2192-L2216

module
public import Mathlib
public import Definitions.Def_RiemannMasullo_LocalIdealClasses
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
open scoped Classical
local notation "Oₛ(" F ", " S ")" => Set.integer (S : Set (Primes(F))) F
local notation "LocalClass(" F ", " v ")" =>
  (HeightOneSpectrum.adicCompletion F v)ˣ ⧸ Submonoid.units (Submonoid.ofClass (HeightOneSpectrum.adicCompletionIntegers F v))

theorem RiemannMasullo.sUnitLocalClasses_eq_one (S T : Finset (Primes(F))) (h : S ⊆ T)
    (u : (T : Set (Primes(F))).unit F) :
    sUnitLocalClasses F T (T \ S) u = 1 ↔ u.val ∈ (S : Set (Primes(F))).unit F := by sorry
