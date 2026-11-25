-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BridgeRealK_sgn_mul_self
-- name    : PI.UnitaryGroupMassFormula.BridgeRealK.sgn_mul_self
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:32.92357+00:00
-- url     : https://prove2.me/theorems/ead8bfda-e322-4a91-b644-fbfbb4afde07
-- title:
--   Bridge Real K: sgn mul self
-- statement:
--   The Bridge Real K construction uses the sgn mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RealFieldComparison/JmMulApply.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RealFieldComparison/JmMulApply.lean#L11-L13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealFieldComparison_JmMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BridgeRealK
open Matrix

theorem PI.UnitaryGroupMassFormula.BridgeRealK.sgn_mul_self {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (if ε a then (1 : ℂ) else -1) * (if ε a then (1 : ℂ) else -1) = 1 := by sorry
