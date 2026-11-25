-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_relIdx_ne_zero_of_le_left
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.relIdx_ne_zero_of_le_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:41:04.534738+00:00
-- url     : https://prove2.me/theorems/defc19f4-f989-48dd-ac2a-7ed7e6159f1f
-- title:
--   Unimod Loc Std: rel Idx ne zero of le left
-- statement:
--   The Unimod Loc Std construction uses the rel Idx ne zero of le left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RelIdxNeZeroOfLeLeft.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RelIdxNeZeroOfLeLeft.lean#L35-L47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.relIdx_ne_zero_of_le_left {A A' B : AddSubgroup V} (h : A ≤ A') (hA : A.relIndex B ≠ 0) :
    A'.relIndex B ≠ 0 := by sorry
