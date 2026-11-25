-- Prove2me | Theorems.Thm_PI_WMI_MMap_evM_rowAct
-- name    : PI.WMI.MMap.evM_rowAct
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:11.961793+00:00
-- url     : https://prove2.me/theorems/528edcd2-93e5-4d9c-9203-c842cd235f14
-- title:
--   MMap: ev M row Act
-- statement:
--   The MMap construction uses the ev M row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L42-L47

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

theorem PI.WMI.MMap.evM_rowAct {N : ℕ} (g A : Matrix (Fin N) (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    evM A (rowAct ℂ (n := N) g f) = evM (g * A) f := by sorry
