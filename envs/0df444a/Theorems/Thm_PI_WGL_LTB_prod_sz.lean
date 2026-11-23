-- Prove2me | Theorems.Thm_PI_WGL_LTB_prod_sz
-- name    : PI.WGL.LTB.prod_sz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:25.039962+00:00
-- url     : https://prove2.me/theorems/05f27548-265f-4fba-a621-b2ecb1c92541
-- title:
--   LTB: prod sz
-- statement:
--   The LTB construction uses the prod sz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L187-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L187-L202

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM

theorem PI.WGL.LTB.prod_sz {M : Type*} [CommMonoid M] {K : ℕ} (sz : Fin K → ℕ) (s : Finset (Fin K)) (bnd : ℕ)
    (hb : ∀ k ∈ s, sz k < bnd) (F : ℕ → M) :
    ∏ k ∈ s, F (sz k) = ∏ y ∈ Finset.range bnd, F y ^ (s.filter fun k => sz k = y).card := by sorry
