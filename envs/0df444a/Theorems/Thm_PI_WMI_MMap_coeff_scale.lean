-- Prove2me | Theorems.Thm_PI_WMI_MMap_coeff_scale
-- name    : PI.WMI.MMap.coeff_scale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:19.538805+00:00
-- url     : https://prove2.me/theorems/f8f5a53c-6015-4af4-b184-945b6034ec05
-- title:
--   MMap: coeff scale
-- statement:
--   The MMap construction uses the coeff scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L79-L87

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

theorem PI.WMI.MMap.coeff_scale {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℂ) (f : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (aeval (fun v : σ => C (w v) * X v) f) = coeff m f * ∏ v, w v ^ m v := by sorry
