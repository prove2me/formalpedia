-- Prove2me | Theorems.Thm_PI_SqPairLocal_nat_notMem
-- name    : PI.SqPairLocal.nat_notMem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:35.472698+00:00
-- url     : https://prove2.me/theorems/889cd7bf-f3eb-5178-b0a1-c0ff7e9397a1
-- title:
--   Sq Pair Local: nat not Mem
-- statement:
--   The Sq Pair Local construction uses the nat not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L192-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L192-L202

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PI.SqPairLocal.nat_notMem {Q : Ideal (𝓞 E)} (hQ : Q.IsMaximal) {p c : ℕ} (hp : p.Prime) (hc : ¬ p ∣ c)
    (hpQ : (p : 𝓞 E) ∈ Q) : (c : 𝓞 E) ∉ Q := by sorry
