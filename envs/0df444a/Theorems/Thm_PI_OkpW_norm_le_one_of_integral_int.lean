-- Prove2me | Theorems.Thm_PI_OkpW_norm_le_one_of_integral_int
-- name    : PI.OkpW.norm_le_one_of_integral_int
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:07.721009+00:00
-- url     : https://prove2.me/theorems/dd49107b-c214-5dc6-9795-46400e275904
-- title:
--   Okp W: norm le one of integral int
-- statement:
--   The Okp W construction uses the norm le one of integral int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L34-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW

theorem PI.OkpW.norm_le_one_of_integral_int {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra ℤ F]
    (δ : F) (h : IsIntegral ℤ δ) : ‖δ‖ ≤ 1 := by sorry
