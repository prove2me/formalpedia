-- Prove2me | Theorems.Thm_PI_SqPairLocal_pres_sub
-- name    : PI.SqPairLocal.pres_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:32:15.0798+00:00
-- url     : https://prove2.me/theorems/f30dc65f-03ad-46d7-b667-139c31fe56f6
-- title:
--   Sq Pair Local: pres sub
-- statement:
--   The Sq Pair Local construction uses the pres sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L31-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
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
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
variable {L : Submodule (𝓞 E) (Fin N → E)}

theorem PI.SqPairLocal.pres_sub {e f : Matrix (Fin N) (Fin N) E} (he : Pres L e) (hf : Pres L f) :
    Pres L (e - f) := by sorry
