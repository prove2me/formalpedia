-- Prove2me | Theorems.Thm_PI_WMI_lowerInv_det_ne
-- name    : PI.WMI.lowerInv_det_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:48:48.988566+00:00
-- url     : https://prove2.me/theorems/07dc41d5-e0af-4613-8741-68de25305fc0
-- title:
--   WMI: lower Inv det ne
-- statement:
--   The WMI construction uses the lower Inv det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L73-L76

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem PI.WMI.lowerInv_det_ne {N : ℕ} (θ : Fin N → ℝ) : (torus θ).det ≠ 0 := by sorry
