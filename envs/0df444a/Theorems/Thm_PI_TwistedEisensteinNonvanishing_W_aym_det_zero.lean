-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_aym_det_zero
-- name    : PI.TwistedEisensteinNonvanishing.W.aym_det_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:45.658852+00:00
-- url     : https://prove2.me/theorems/bdf0f31c-ce8b-498e-8138-40b42bf0ddc5
-- title:
--   W: aym det zero
-- statement:
--   The W construction uses the aym det zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TestFunctionPeriodicity.lean#L42-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TestFunctionPeriodicity.lean#L42-L75

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
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem PI.TwistedEisensteinNonvanishing.W.aym_det_zero (q k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) (hr : n + c < r ∨ n' + c' < r) :
    (AYm q k₀ r c' n' c n x).det = 0 := by sorry
