-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_T2_exists_dec_equiv
-- name    : ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:30:14.660805+00:00
-- url     : https://prove2.me/theorems/477d4a7c-9d2e-4d6f-9c5a-6a1ca3174b46
-- title:
--   T2: exists dec equiv
-- statement:
--   The T2 construction uses the exists dec equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/TraceFormulas/LatDefs.lean#L337-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/TraceFormulas/LatDefs.lean#L337-L344

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_CharacterSplitJumps_Statement
import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_TraceFormulas_LatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T2
open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable [hT2Core : Fact Core]

theorem ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv {p : ℕ} [Fact p.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (i : ↥(A.decompositionSubgroup F) ≃ₜ* GK p K),
      (∀ (O : Type) [CommRing O] (ε : ↥(A.decompositionSubgroup F) →* Oˣ),
        IsCycOn p (A.decompositionSubgroup F) ε → IsCyc p K (carry i ε)) ∧
      (∀ g : ↥(A.decompositionSubgroup F), i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v → Module.finrank ℚ_[p] K = locDeg v := by sorry
