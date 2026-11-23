-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_smul_left
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.mj_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:49.287443+00:00
-- url     : https://prove2.me/theorems/b5fa88ce-2433-4a13-9337-c63a20e98378
-- title:
--   Slope Test Remaining Choices: mj smul left
-- statement:
--   The Slope Test Remaining Choices construction uses the mj smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean#L25-L27

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

theorem PI.AutLzFinite.SlopeTestRemainingChoices.mj_smul_left (z : S.V) (c : E) (x y : S.V) : mj S z (c • x) y = star c * mj S z x y := by sorry
