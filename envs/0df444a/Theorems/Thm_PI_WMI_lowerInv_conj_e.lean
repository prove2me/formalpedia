-- Prove2me | Theorems.Thm_PI_WMI_lowerInv_conj_e
-- name    : PI.WMI.lowerInv_conj_e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:47:19.348996+00:00
-- url     : https://prove2.me/theorems/ff716c67-3f19-4364-988b-0c6b971a445e
-- title:
--   WMI: lower Inv conj e
-- statement:
--   The WMI construction uses the lower Inv conj e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L18-L22

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

theorem PI.WMI.lowerInv_conj_e (r : ℝ) : (starRingEnd ℂ) (lowerInv_e r) = lowerInv_e (-r) := by sorry
