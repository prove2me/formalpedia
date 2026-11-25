-- Prove2me | Theorems.Thm_PI_SqPairLocal_pres_conj
-- name    : PI.SqPairLocal.pres_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:25:37.300814+00:00
-- url     : https://prove2.me/theorems/51e08f9d-00df-4ced-8767-23acaffc7c1e
-- title:
--   Sq Pair Local: pres conj
-- statement:
--   The Sq Pair Local construction uses the pres conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L73-L82

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

theorem PI.SqPairLocal.pres_conj (hL : IsSDG E N L) {e : Matrix (Fin N) (Fin N) E} (he : Pres L e) :
    Pres L eᴴ := by sorry
