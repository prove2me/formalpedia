-- Prove2me | Theorems.Thm_PI_WMI_MMap_eval_aeval_eq
-- name    : PI.WMI.MMap.eval_aeval_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:13.856582+00:00
-- url     : https://prove2.me/theorems/240fd43b-6452-40d9-8897-7fee852456c2
-- title:
--   MMap: eval aeval eq
-- statement:
--   The MMap construction uses the eval aeval eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L12-L17

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

theorem PI.WMI.MMap.eval_aeval_eq {σ τ : Type*} (y : τ → ℂ) (g : σ → MvPolynomial τ ℂ) (f : MvPolynomial σ ℂ) :
    eval y (aeval g f) = eval (fun i => eval y (g i)) f := by sorry
