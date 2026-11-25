-- Prove2me | Theorems.Thm_PI_WGL_embGL_ll
-- name    : PI.WGL.embGL_ll
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:50:19.967526+00:00
-- url     : https://prove2.me/theorems/51529acf-f3fd-4938-b507-b6460f571cc2
-- title:
--   WGL: emb GL ll
-- statement:
--   The WGL construction uses the emb GL ll property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliEqv.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliEqv.lean#L22-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
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

theorem PI.WGL.embGL_ll {n : ℕ} (g : GL (Fin n) ℂ) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n) = 1 := by sorry
