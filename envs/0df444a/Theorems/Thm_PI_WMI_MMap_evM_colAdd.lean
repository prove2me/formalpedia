-- Prove2me | Theorems.Thm_PI_WMI_MMap_evM_colAdd
-- name    : PI.WMI.MMap.evM_colAdd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:06:41.935936+00:00
-- url     : https://prove2.me/theorems/0c0b5ff3-2d02-49f4-8cae-3c64b9264e97
-- title:
--   MMap: ev M col Add
-- statement:
--   The MMap construction uses the ev M col Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L49-L59

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

theorem PI.WMI.MMap.evM_colAdd {N : ℕ} (l j : Fin N) (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (colAdd ℂ (r := N) l j c f) = evM (A * (1 + Matrix.single l j c)) f := by sorry
