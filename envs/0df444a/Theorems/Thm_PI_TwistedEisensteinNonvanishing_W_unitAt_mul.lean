-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_unitAt_mul
-- name    : PI.TwistedEisensteinNonvanishing.W.unitAt_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:29:30.870343+00:00
-- url     : https://prove2.me/theorems/3233b2bf-dc13-4474-a573-8842d8820d4a
-- title:
--   W: unit At mul
-- statement:
--   The W construction uses the unit At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IaDivDown.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IaDivDown.lean#L111-L112

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
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
open Loc LocE
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
variable {P}

theorem PI.TwistedEisensteinNonvanishing.W.unitAt_mul {w w' : E} (h : UnitAt P w) (h' : UnitAt P w') : UnitAt P (w * w') := by sorry
