-- Prove2me | Theorems.Thm_RiemannMasullo_localIdealClass_normalization
-- name    : RiemannMasullo.localIdealClass_normalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T01:56:01.486557+00:00
-- url     : https://prove2.me/theorems/53548234-4b6b-415e-907b-c97a2210279c
-- title:
--   Riemann Masullo: local Ideal Class normalization
-- statement:
--   Paper: Equation (A.1.5.9), p. 544. A local unit contributes the identity and a
--   uniformizer contributes the class of the prime to the first power.
--
--   Source: https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L2226-L2236
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L2226-L2236

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

theorem RiemannMasullo.localIdealClass_normalization (v : Primes(F)) (x : (v.adicCompletion F)ˣ) :
    (x ∈ (v.adicCompletionIntegers F).units → localIdealClass F v x = 1) ∧
    (Valued.v x.val = WithZero.exp (-1 : ℤ) → localIdealClass F v x =
      ClassGroup.equivPic (𝓞 F) (ClassGroup.mk0
        ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) := by sorry
