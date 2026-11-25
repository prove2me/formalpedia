-- Prove2me | Theorems.Thm_PI_WGL_lm_last_of_row
-- name    : PI.WGL.lm_last_of_row
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:19.309231+00:00
-- url     : https://prove2.me/theorems/a5e5c1a8-821c-59d8-b035-5bcf7683a0de
-- title:
--   WGL: lm last of row
-- statement:
--   The WGL construction uses the lm last of row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L86-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L86-L95

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm
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

theorem PI.WGL.lm_last_of_row {N : ℕ} (hN : 0 < N) (f : MvPolynomial (Fin N × Fin N) ℂ) (ω : Fin N → ℕ)
    (hf : IsWeightedHomogeneous (rowW N N) f ω) :
    IsWeightedHomogeneous (lastW N) f (ω ⟨N - 1, by omega⟩) := by sorry
