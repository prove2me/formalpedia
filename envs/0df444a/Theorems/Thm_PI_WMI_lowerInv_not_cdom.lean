-- Prove2me | Theorems.Thm_PI_WMI_lowerInv_not_cdom
-- name    : PI.WMI.lowerInv_not_cdom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:59:29.975365+00:00
-- url     : https://prove2.me/theorems/26a38a7a-34b5-5a10-8d79-88e9b8a5ccf9
-- title:
--   WMI: lower Inv not cdom
-- statement:
--   The WMI construction uses the lower Inv not cdom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L117-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L117-L143

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

theorem PI.WMI.lowerInv_not_cdom {N : ℕ} {Λ : Fin N → ℝ} {a b : Fin N} (hab : a < b) {m : ℕ} (hm : 1 ≤ m) :
    ¬ CDom (allPos N) (Λ + (m : ℝ) • root a b) Λ := by sorry
