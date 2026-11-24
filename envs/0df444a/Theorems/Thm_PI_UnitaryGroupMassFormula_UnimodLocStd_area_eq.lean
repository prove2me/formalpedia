-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_area_eq
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.area_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:54:13.040303+00:00
-- url     : https://prove2.me/theorems/abdc228d-aec9-44ee-b3b9-3eacc4510c1d
-- title:
--   Unimod Loc Std: area eq
-- statement:
--   The Unimod Loc Std construction uses the area eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SelfDualStd.lean#L48-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SelfDualStd.lean#L48-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.area_eq (L : PeriodPair) : area L = |detD L| := by sorry
