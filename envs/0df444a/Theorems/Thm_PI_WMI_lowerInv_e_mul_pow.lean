-- Prove2me | Theorems.Thm_PI_WMI_lowerInv_e_mul_pow
-- name    : PI.WMI.lowerInv_e_mul_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:47:37.919379+00:00
-- url     : https://prove2.me/theorems/c52d8081-8817-4453-a3b5-f0dc98472254
-- title:
--   WMI: lower Inv e mul pow
-- statement:
--   The WMI construction uses the lower Inv e mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L12-L16

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

theorem PI.WMI.lowerInv_e_mul_pow (r s : ℝ) (m : ℕ) :
    lowerInv_e r * lowerInv_e s ^ m = lowerInv_e (r + m * s) := by sorry
