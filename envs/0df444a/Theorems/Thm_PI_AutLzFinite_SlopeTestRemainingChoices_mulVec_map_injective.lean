-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mulVec_map_injective
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.mulVec_map_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:54.095796+00:00
-- url     : https://prove2.me/theorems/52ad7338-ae74-5dc7-8be1-8178e12f0fff
-- title:
--   Slope Test Remaining Choices: mul Vec map injective
-- statement:
--   The Slope Test Remaining Choices construction uses the mul Vec map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MulVecMapInjective.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MulVecMapInjective.lean#L51-L54

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

theorem PI.AutLzFinite.SlopeTestRemainingChoices.mulVec_map_injective {K : Type} [Field K] {n k : Type} [Fintype n] [DecidableEq n] [Fintype k]
    [DecidableEq k] (f : K →+* ℂ) (A : Matrix n k K) (hA : Function.Injective A.mulVec) :
    Function.Injective (A.map f).mulVec := by sorry
