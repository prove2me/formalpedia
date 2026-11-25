-- Prove2me | Theorems.Thm_PI_WMI_lowerInv_comm
-- name    : PI.WMI.lowerInv_comm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:00:00.265517+00:00
-- url     : https://prove2.me/theorems/fb25b98d-4d3f-554e-be94-1309507c4b8d
-- title:
--   WMI: lower Inv comm
-- statement:
--   The WMI construction uses the lower Inv comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L78-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/LowerInv.lean#L78-L95

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

theorem PI.WMI.lowerInv_comm {N : ℕ} {a b : Fin N} (hab : a < b) (θ : Fin N → ℝ) (c : ℂ) :
    (1 + Matrix.single b a c) * torus θ =
      torus θ * (1 + Matrix.single b a (c * lowerInv_e (θ a - θ b))) := by sorry
