-- Prove2me | Theorems.Thm_UpperTheory_V_LDataCardLeFinrank_mem_ShaAbs
-- name    : UpperTheory.V.LDataCardLeFinrank.mem_ShaAbs
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:13:00.806176+00:00
-- url     : https://prove2.me/theorems/2e65312b-38b5-52b8-9008-e17e9417c36b
-- title:
--   LData Card Le Finrank: mem Sha Abs
-- statement:
--   The LData Card Le Finrank construction uses the mem Sha Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean#L47-L53

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology
open UpperTheory UpperTheory.V UpperTheory.V.LDataCardLeFinrank
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem UpperTheory.V.LDataCardLeFinrank.mem_ShaAbs (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F))) (x : H1 ρ) :
    x ∈ ShaAbs ρ S ↔
      (∀ v ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val x = 0) ∧
      ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        resH1 ρ (Ine (F := F) A).subtype continuous_subtype_val x = 0 := by sorry
