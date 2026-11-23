-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_add_left
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.mj_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:45.899803+00:00
-- url     : https://prove2.me/theorems/85c22836-e515-43cf-90d9-0c2fdbde4c38
-- title:
--   Slope Test Remaining Choices: mj add left
-- statement:
--   The Slope Test Remaining Choices construction uses the mj add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean#L21-L23

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

theorem PI.AutLzFinite.SlopeTestRemainingChoices.mj_add_left (z x x' y : S.V) : mj S z (x + x') y = mj S z x y + mj S z x' y := by sorry
