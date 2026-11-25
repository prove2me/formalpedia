-- Prove2me | Theorems.Thm_PI_WMI_MMap_evM_scale
-- name    : PI.WMI.MMap.evM_scale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:49.26756+00:00
-- url     : https://prove2.me/theorems/9c8a2400-225d-45d9-818b-40e44ead4e54
-- title:
--   MMap: ev M scale
-- statement:
--   The MMap construction uses the ev M scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L61-L67

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

theorem PI.WMI.MMap.evM_scale {N : ℕ} (t : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (aeval (fun v : Fin N × Fin N => C (t v.2) * X v) f) = evM (A * Matrix.diagonal t) f := by sorry
