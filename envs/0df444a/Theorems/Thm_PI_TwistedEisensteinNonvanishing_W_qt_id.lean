-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_id
-- name    : PI.TwistedEisensteinNonvanishing.W.qt_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:16.877992+00:00
-- url     : https://prove2.me/theorems/f2bce19c-291a-4a58-a3fc-2d189aecd32c
-- title:
--   W: qt id
-- statement:
--   The W construction uses the qt id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/ChangeVariablesDeterminantOne.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/ChangeVariablesDeterminantOne.lean#L13-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_ChangeVariablesDeterminantOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function Matrix
variable {E K : Type} [Field E] [NumberField E] [Field K]

theorem PI.TwistedEisensteinNonvanishing.W.qt_id {P : HeightOneSpectrum (𝓞 E)} {ι : Type} [Fintype ι] [DecidableEq ι] :
    QT P (fun t : ι → E => t) (1 : K) := by sorry
