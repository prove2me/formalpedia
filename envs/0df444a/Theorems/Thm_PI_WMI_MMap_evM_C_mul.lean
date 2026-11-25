-- Prove2me | Theorems.Thm_PI_WMI_MMap_evM_C_mul
-- name    : PI.WMI.MMap.evM_C_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:58.971028+00:00
-- url     : https://prove2.me/theorems/66cb865d-ea3e-46fe-b6f9-a483d1489787
-- title:
--   MMap: ev M C mul
-- statement:
--   The MMap construction uses the ev M C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L33-L35

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

theorem PI.WMI.MMap.evM_C_mul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (C c * p) = c * evM A p := by sorry
