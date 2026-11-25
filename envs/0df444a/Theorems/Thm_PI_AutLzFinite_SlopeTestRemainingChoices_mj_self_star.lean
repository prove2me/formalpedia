-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_self_star
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.mj_self_star
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:22.939343+00:00
-- url     : https://prove2.me/theorems/3ae71d42-c7ee-4865-81b6-ee6b3fef0432
-- title:
--   Slope Test Remaining Choices: mj self star
-- statement:
--   The Slope Test Remaining Choices construction uses the mj self star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean#L44-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean#L44-L44

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
variable {S}

theorem PI.AutLzFinite.SlopeTestRemainingChoices.mj_self_star (z x : S.V) : star (mj S z x x) = mj S z x x := by sorry
