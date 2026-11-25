-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isFrob_restrictScalars_of_prime_absNorm__d18c10b9c1f0
-- name    : P2M_GlobalTheory_T_isFrob_restrictScalars_of_prime_absNorm__d18c10b9c1f0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:38.278551+00:00
-- url     : https://prove2.me/theorems/4049d982-e8e3-4ffa-a618-37d85fb9c0fb
-- title:
--   P2 M Global Theory T is Frob restrict Scalars of prime abs Norm  d18c10b9c1f0: P2 M Global Theory T is Frob restrict Scalars of prime abs Norm  d18c10b9c1f0
-- statement:
--   The P2 M Global Theory T is Frob restrict Scalars of prime abs Norm  d18c10b9c1f0 construction uses the P2 M Global Theory T is Frob restrict Scalars of prime abs Norm  d18c10b9c1f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFrobRestrictScalarsOfPrimeAbsNormStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFrobRestrictScalarsOfPrimeAbsNormStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFrobRestrictScalarsOfPrimeAbsNorm
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFrobRestrictScalarsOfPrimeAbsNormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_isFrob_restrictScalars_of_prime_absNorm__d18c10b9c1f0 : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Z : IntermediateField F Ω) [NumberField Z] (w : HeightOneSpectrum (𝓞 Z)) (v : HeightOneSpectrum (𝓞 F)), w.asIdeal.LiesOver v.asIdeal → (Ideal.absNorm w.asIdeal).Prime → ∀ B : ValuationSubring Ω, IsPlaceOver (F := Z) B w → ∀ σ : G Z Ω, IsFrob B (normV w) σ → Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal ∧ IsPlaceOver (F := F) B v ∧ IsFrob (F := F) B (normV v) (σ.restrictScalars F) := by sorry

alias «GlobalTheory».«T».«isFrob_restrictScalars_of_prime_absNorm'» := P2M_GlobalTheory_T_isFrob_restrictScalars_of_prime_absNorm__d18c10b9c1f0
