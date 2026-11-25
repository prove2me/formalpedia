-- Prove2me | Theorems.Thm_UpperTheory_prod_cmType_eq_norm_and_weightCongruence_one
-- name    : UpperTheory.prod_cmType_eq_norm_and_weightCongruence_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:58.681983+00:00
-- url     : https://prove2.me/theorems/56be7ddb-9ecd-4cac-ae5b-65bb397092ef
-- title:
--   Upper Theory: prod cm Type eq norm and weight Congruence one
-- statement:
--   The Upper Theory construction uses the prod cm Type eq norm and weight Congruence one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdCmTypeEqNormAndWeightCongruenceOne.lean#L44-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdCmTypeEqNormAndWeightCongruenceOne.lean#L44-L62

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions

theorem UpperTheory.prod_cmType_eq_norm_and_weightCongruence_one :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi),
      (∀ x : H.E, ∏ τ, H.sigmaOf ((eT τ : R.Psi) : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x)) ∧
      UpperTheory.MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => 1) := by sorry
