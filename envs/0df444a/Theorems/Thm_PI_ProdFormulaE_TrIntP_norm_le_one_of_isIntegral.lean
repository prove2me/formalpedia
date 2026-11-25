-- Prove2me | Theorems.Thm_PI_ProdFormulaE_TrIntP_norm_le_one_of_isIntegral
-- name    : PI.ProdFormulaE.TrIntP.norm_le_one_of_isIntegral
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:18:35.478193+00:00
-- url     : https://prove2.me/theorems/891d3134-8cf4-40e5-853b-2e38bdfea96d
-- title:
--   Tr Int P: norm le one of is Integral
-- statement:
--   The Tr Int P construction uses the norm le one of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/NormTraceLeOne.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/NormTraceLeOne.lean#L8-L13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormTraceLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ProdFormulaE PI.ProdFormulaE.TrIntP

theorem PI.ProdFormulaE.TrIntP.norm_le_one_of_isIntegral {ℓ : ℕ} [Fact ℓ.Prime] {t : ℚ_[ℓ]} (ht : IsIntegral ℤ t) :
    ‖t‖ ≤ 1 := by sorry
