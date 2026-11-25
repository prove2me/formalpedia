-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_product_haar_measure_holds
-- name    : PI.VolSemiDirect.W.product_haar_measure_holds
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:22.246151+00:00
-- url     : https://prove2.me/theorems/1b28a15b-9a14-4721-ab47-20b48093ba00
-- title:
--   W: product haar measure holds
-- statement:
--   The W construction uses the product haar measure holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProdHaar.lean#L11-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProdHaar.lean#L11-L99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_VolumeQuotientHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProdHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open MeasureTheory

theorem PI.VolSemiDirect.W.product_haar_measure_holds : ProdHaarG := by sorry
