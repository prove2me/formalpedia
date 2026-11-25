-- Prove2me | Theorems.Thm_UpperTheory_Mu_exists_shift
-- name    : UpperTheory.Mu.exists_shift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:48:46.859834+00:00
-- url     : https://prove2.me/theorems/28573702-c795-4c54-8346-57e975d28319
-- title:
--   Mu: exists shift
-- statement:
--   The Mu construction uses the exists shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/IsRootOfIntegral.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/IsRootOfIntegral.lean#L33-L35

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

theorem UpperTheory.Mu.exists_shift [DecidableEq ι] (a : ι → ℤ) (τ₀ : ι) : ∃ s : ℕ, s < Units.torsionOrder H.E ∧
    MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun τ => a τ + if τ = τ₀ then (s : ℤ) else 0) := by sorry
