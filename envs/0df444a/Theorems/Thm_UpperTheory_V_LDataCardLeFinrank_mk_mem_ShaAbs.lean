-- Prove2me | Theorems.Thm_UpperTheory_V_LDataCardLeFinrank_mk_mem_ShaAbs
-- name    : UpperTheory.V.LDataCardLeFinrank.mk_mem_ShaAbs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:42:08.930168+00:00
-- url     : https://prove2.me/theorems/d030805b-606e-4ef9-86bb-0da04df55004
-- title:
--   LData Card Le Finrank: mk mem Sha Abs
-- statement:
--   The LData Card Le Finrank construction uses the mk mem Sha Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean#L60-L66

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

theorem UpperTheory.V.LDataCardLeFinrank.mk_mem_ShaAbs (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F))) (z : Z1 ρ) :
    (Submodule.Quotient.mk z : H1 ρ) ∈ ShaAbs ρ S ↔
      (∀ v ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∃ m, ∀ g ∈ Dec (F := F) A, z.1 g = ρ g m - m) ∧
      ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∃ m, ∀ g ∈ Ine (F := F) A, z.1 g = ρ g m - m := by sorry
