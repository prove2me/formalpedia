-- Prove2me | Theorems.Thm_PI_AprimeInfW_ST_arg_exp_small
-- name    : PI.AprimeInfW.ST.arg_exp_small
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:12:52.613064+00:00
-- url     : https://prove2.me/theorems/e3f05493-94ce-44b6-b857-6eea711a700d
-- title:
--   ST: arg exp small
-- statement:
--   The ST construction uses the arg exp small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/SdTest.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/SdTest.lean#L58-L60

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdFurther_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_SdTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW PI.AprimeInfW.ST
open MeasureTheory
open MeasureTheory Complex Filter Topology
open scoped RealInnerProductSpace
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem PI.AprimeInfW.ST.arg_exp_small {θ : ℝ} (h : θ ∈ Set.Ioo (-Real.pi) Real.pi) : arg (exp (↑θ * I)) = θ := by sorry
