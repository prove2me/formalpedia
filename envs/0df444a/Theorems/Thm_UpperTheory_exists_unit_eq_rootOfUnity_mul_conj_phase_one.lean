-- Prove2me | Theorems.Thm_UpperTheory_exists_unit_eq_rootOfUnity_mul_conj_phase_one
-- name    : UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:14:48.456187+00:00
-- url     : https://prove2.me/theorems/aa045545-bba5-4c69-850c-86f6390f5878
-- title:
--   Upper Theory: exists unit eq root Of Unity mul conj phase one
-- statement:
--   The Upper Theory construction uses the exists unit eq root Of Unity mul conj phase one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ExistsUnitEqRootOfUnityMulConjPhaseOne.lean#L69-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ExistsUnitEqRootOfUnityMulConjPhaseOne.lean#L69-L108

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcEqOfPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_RootOfUnityGaloisActionCMDatum
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypePhaseOneAddRootOfUnity
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ExistsUnitEqRootOfUnityMulConjPhaseOne
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions

theorem UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) →
      ∃ δ : (H.E)ˣ, (δ : H.E) = z * H.conj (δ : H.E) ∧
        (∀ P : HeightOneSpectrum (𝓞 H.E), ((H.condN : ℕ) : 𝓞 H.E) ∉ P.asIdeal → P.valuation H.E (δ : H.E) = 1) ∧
        ∏ τ, (H.emb ((eT τ : R.Psi) : R.GG) (δ : H.E) / ((‖H.emb ((eT τ : R.Psi) : R.GG) (δ : H.E)‖ : ℝ) : ℂ)) = 1 := by sorry
