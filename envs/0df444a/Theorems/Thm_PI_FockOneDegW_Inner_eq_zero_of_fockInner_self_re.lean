-- Prove2me | Theorems.Thm_PI_FockOneDegW_Inner_eq_zero_of_fockInner_self_re
-- name    : PI.FockOneDegW.Inner.eq_zero_of_fockInner_self_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:55.116884+00:00
-- url     : https://prove2.me/theorems/bb35b39c-c23d-43e4-af9c-d775c60074b1
-- title:
--   Inner: eq zero of fock Inner self re
-- statement:
--   The Inner construction uses the eq zero of fock Inner self re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/EqZeroOfFockInnerSelfRe.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/EqZeroOfFockInnerSelfRe.lean#L41-L51

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

theorem PI.FockOneDegW.Inner.eq_zero_of_fockInner_self_re (F : MvPolynomial σ ℂ) (h : (fockInner F F).re = 0) :
    F = 0 := by sorry
