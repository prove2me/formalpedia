-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_sum_rowDeg_of_mem
-- name    : PI.WGL.EqvWt.sum_rowDeg_of_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:08.549129+00:00
-- url     : https://prove2.me/theorems/b97bbb02-5398-41e3-8342-ce88c2aaec59
-- title:
--   Eqv Wt: sum row Deg of mem
-- statement:
--   The Eqv Wt construction uses the sum row Deg of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L100-L109

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt

theorem PI.WGL.EqvWt.sum_rowDeg_of_mem {r : ℕ} (lam : DomWeight r) (f : MvPolynomial (Fin r × Fin r) ℂ)
    (hf : f ∈ nablaSq ℂ r lam) (m : Fin r × Fin r →₀ ℕ) (hm : coeff m f ≠ 0) :
    ∑ a, rowDeg m a = ∑ j, lam.natW j := by sorry
