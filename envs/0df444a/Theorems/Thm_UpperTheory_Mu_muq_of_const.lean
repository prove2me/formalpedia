-- Prove2me | Theorems.Thm_UpperTheory_Mu_muq_of_const
-- name    : UpperTheory.Mu.muq_of_const
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:23:53.23446+00:00
-- url     : https://prove2.me/theorems/51520ef9-7818-4415-aee9-112c5c58f8d5
-- title:
--   Mu: muq of const
-- statement:
--   The Mu construction uses the muq of const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/IsRootOfIntegral.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/IsRootOfIntegral.lean#L26-L27

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

theorem UpperTheory.Mu.muq_of_const {e : ι → ℚ} (c : ℤ) (he : ∀ τ, e τ = c) : MUQ (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) e := by sorry
