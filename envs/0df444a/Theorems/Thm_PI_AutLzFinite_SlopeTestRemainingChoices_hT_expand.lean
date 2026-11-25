-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_hT_expand
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.hT_expand
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:01.514843+00:00
-- url     : https://prove2.me/theorems/d6ed7524-3b80-4b10-8d5f-c7cd859db6d3
-- title:
--   Slope Test Remaining Choices: h T expand
-- statement:
--   The Slope Test Remaining Choices construction uses the h T expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MulVecMapInjective.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MulVecMapInjective.lean#L14-L30

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

theorem PI.AutLzFinite.SlopeTestRemainingChoices.hT_expand (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * S.gram i j * S.frame.repr y j := by sorry
