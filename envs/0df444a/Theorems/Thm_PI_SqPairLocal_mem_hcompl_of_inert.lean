-- Prove2me | Theorems.Thm_PI_SqPairLocal_mem_hcompl_of_inert
-- name    : PI.SqPairLocal.mem_hcompl_of_inert
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:57.960529+00:00
-- url     : https://prove2.me/theorems/ca364c35-8276-475e-a5c8-834949b6ab19
-- title:
--   Sq Pair Local: mem hcompl of inert
-- statement:
--   The Sq Pair Local construction uses the mem hcompl of inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnimodularOfIsSDG.lean#L31-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnimodularOfIsSDG.lean#L31-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnimodGenus
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnimodularOfIsSDG
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
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG PI.UG
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PI.SqPairLocal.mem_hcompl_of_inert {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) (s : 𝓞 E) :
    s ∈ hcompl (K := E) Q ↔ s ∉ Q := by sorry
