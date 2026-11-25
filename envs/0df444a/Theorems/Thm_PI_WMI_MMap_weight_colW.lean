-- Prove2me | Theorems.Thm_PI_WMI_MMap_weight_colW
-- name    : PI.WMI.MMap.weight_colW
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:30.189797+00:00
-- url     : https://prove2.me/theorems/c9239f27-2faf-4657-a3e1-33fcb6496377
-- title:
--   MMap: weight col W
-- statement:
--   The MMap construction uses the weight col W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L118-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L118-L124

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

theorem PI.WMI.MMap.weight_colW {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (s : Fin N) :
    Finsupp.weight (colW N N) m s = ∑ v : Fin N × Fin N, if v.2 = s then m v else 0 := by sorry
