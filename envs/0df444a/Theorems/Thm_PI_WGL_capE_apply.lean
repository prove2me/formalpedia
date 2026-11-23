-- Prove2me | Theorems.Thm_PI_WGL_capE_apply
-- name    : PI.WGL.capE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:17.837026+00:00
-- url     : https://prove2.me/theorems/36926acd-fb7f-4363-8400-986733111eb7
-- title:
--   WGL: cap E apply
-- statement:
--   The WGL construction uses the cap E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliShift.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliShift.lean#L62-L68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
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

theorem PI.WGL.capE_apply {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) (x : MvPolynomial (Fin N × Fin N) ℂ) :
    capE h lam a b x = pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) x +
      if a = b then (lam.detShift : ℂ) • x else 0 := by sorry
