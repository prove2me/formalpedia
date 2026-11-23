-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_herm_swap
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.herm_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:50.765471+00:00
-- url     : https://prove2.me/theorems/edf8ad1a-98d5-45c0-8fc9-473ad2567c0b
-- title:
--   Slope Test Remaining Choices: herm swap
-- statement:
--   The Slope Test Remaining Choices construction uses the herm swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MulVecMapInjective.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MulVecMapInjective.lean#L32-L33

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe
import Definitions.Def_Lemmata_GeneralBFactUpperAltForm_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
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
open Matrix Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem PI.AutLzFinite.SlopeTestRemainingChoices.herm_swap (x y : S.V) : S.hT y x = star (S.hT x y) := by sorry
