-- Prove2me | Theorems.Thm_UpperTheory_Mu_mu_const
-- name    : UpperTheory.Mu.mu_const
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:03:49.811802+00:00
-- url     : https://prove2.me/theorems/7d8e85d9-83f3-4793-8178-0f3d4d95648f
-- title:
--   Mu: mu const
-- statement:
--   The Mu construction uses the mu const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/IsRootOfIntegral.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/IsRootOfIntegral.lean#L15-L15

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

theorem UpperTheory.Mu.mu_const (c : ℤ) : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => c) := by sorry
