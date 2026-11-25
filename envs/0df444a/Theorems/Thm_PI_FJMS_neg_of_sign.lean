-- Prove2me | Theorems.Thm_PI_FJMS_neg_of_sign
-- name    : PI.FJMS.neg_of_sign
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:47.793789+00:00
-- url     : https://prove2.me/theorems/c39cb29a-5eff-419f-9df8-788abce65399
-- title:
--   FJMS: neg of sign
-- statement:
--   The FJMS construction uses the neg of sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsBlockHighestWeight.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsBlockHighestWeight.lean#L13-L16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsBlockHighestWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP

theorem PI.FJMS.neg_of_sign {x : ℚ} {b : Bool} (hb : b = false) (h0 : x ≠ 0) (h : b = true ↔ 0 < x) : x < 0 := by sorry
