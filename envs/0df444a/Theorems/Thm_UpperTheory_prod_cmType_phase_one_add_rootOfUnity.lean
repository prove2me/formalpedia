-- Prove2me | Theorems.Thm_UpperTheory_prod_cmType_phase_one_add_rootOfUnity
-- name    : UpperTheory.prod_cmType_phase_one_add_rootOfUnity
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:14:59.329633+00:00
-- url     : https://prove2.me/theorems/5aa21765-d21a-4dde-96c6-06cbac5e3c43
-- title:
--   Upper Theory: prod cm Type phase one add root Of Unity
-- statement:
--   The Upper Theory construction uses the prod cm Type phase one add root Of Unity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdCmTypePhaseOneAddRootOfUnity.lean#L39-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdCmTypePhaseOneAddRootOfUnity.lean#L39-L73

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_RootOfUnityGaloisActionCMDatum
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypePhaseOneAddRootOfUnity
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions

theorem UpperTheory.prod_cmType_phase_one_add_rootOfUnity :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → z ≠ -1 →
      ∏ τ, (H.emb ((eT τ : R.Psi) : R.GG) (1 + z) / ((‖H.emb ((eT τ : R.Psi) : R.GG) (1 + z)‖ : ℝ) : ℂ)) = 1 := by sorry
