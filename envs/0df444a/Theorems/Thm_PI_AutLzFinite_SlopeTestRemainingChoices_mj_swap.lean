-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_swap
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.mj_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:50.485368+00:00
-- url     : https://prove2.me/theorems/5c491b0f-bb31-4692-b5a8-cff9e0641c93
-- title:
--   Slope Test Remaining Choices: mj swap
-- statement:
--   The Slope Test Remaining Choices construction uses the mj swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MjSmulRight.lean#L37-L42

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

theorem PI.AutLzFinite.SlopeTestRemainingChoices.mj_swap (z x y : S.V) : mj S z y x = star (mj S z x y) := by sorry
