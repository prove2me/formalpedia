-- Prove2me | Theorems.Thm_PI_FockOneDegW_Inner_fockInner_self_im
-- name    : PI.FockOneDegW.Inner.fockInner_self_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:23.361669+00:00
-- url     : https://prove2.me/theorems/ce0dbbf1-511b-40aa-a77e-329a86fe9851
-- title:
--   Inner: fock Inner self im
-- statement:
--   The Inner construction uses the fock Inner self im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/EqZeroOfFockInnerSelfRe.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/EqZeroOfFockInnerSelfRe.lean#L38-L39

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action FockRaiseLowInner
open PI PI.FockOneDegW PI.FockOneDegW.Inner
variable {σ : Type*}

theorem PI.FockOneDegW.Inner.fockInner_self_im (F : MvPolynomial σ ℂ) : (fockInner F F).im = 0 := by sorry
