-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_test_function_support
-- name    : PI.TwistedEisensteinNonvanishing.W.test_function_support
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:02.23789+00:00
-- url     : https://prove2.me/theorems/d543f862-63d3-4d5b-a42b-d2a8a1bdf871
-- title:
--   W: test function support
-- statement:
--   The W construction uses the test function support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TestFunctionPeriodicity.lean#L79-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TestFunctionPeriodicity.lean#L79-L90

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TestFunctionPeriodicity
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

theorem PI.TwistedEisensteinNonvanishing.W.test_function_support : PhiSuppP := by sorry
