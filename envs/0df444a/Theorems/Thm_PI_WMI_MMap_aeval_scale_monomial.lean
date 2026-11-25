-- Prove2me | Theorems.Thm_PI_WMI_MMap_aeval_scale_monomial
-- name    : PI.WMI.MMap.aeval_scale_monomial
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:14.074483+00:00
-- url     : https://prove2.me/theorems/3bdc8761-d59a-4f02-8887-e256ad1e00c0
-- title:
--   MMap: aeval scale monomial
-- statement:
--   The MMap construction uses the aeval scale monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L69-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L69-L77

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
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
open PI.WMI.MMap

theorem PI.WMI.MMap.aeval_scale_monomial {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℂ) (u : σ →₀ ℕ) (c : ℂ) :
    aeval (fun v : σ => C (w v) * X v) (monomial u c) = monomial u (c * ∏ v, w v ^ u v) := by sorry
