-- Prove2me | Theorems.Thm_UpperTheory_Mu_prod_emb_zpow
-- name    : UpperTheory.Mu.prod_emb_zpow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:47:20.797918+00:00
-- url     : https://prove2.me/theorems/33fb295e-14fb-4fc9-9017-e4710f7593fa
-- title:
--   Mu: prod emb zpow
-- statement:
--   The Mu construction uses the prod emb zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/IsRootOfIntegral.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/IsRootOfIntegral.lean#L17-L18

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ExistsShiftWeightCongruenceLtTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_IsRootOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.BasicNotions
open UpperTheory UpperTheory.Mu
variable {R : Ranks} (H : Host R) {ι : Type} [Fintype ι] (eT : ι ≃ R.Psi)

theorem UpperTheory.Mu.prod_emb_zpow {z : H.E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) (c : ℤ) :
    ∏ τ, H.emb ((eT τ : R.Psi) : R.GG) z ^ c = 1 := by sorry
