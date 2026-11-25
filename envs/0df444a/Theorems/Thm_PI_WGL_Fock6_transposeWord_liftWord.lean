-- Prove2me | Theorems.Thm_PI_WGL_Fock6_transposeWord_liftWord
-- name    : PI.WGL.Fock6.transposeWord_liftWord
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:46:35.608152+00:00
-- url     : https://prove2.me/theorems/fac976ce-f139-4acd-927b-11194c0ab625
-- title:
--   Fock6: transpose Word lift Word
-- statement:
--   The Fock6 construction uses the transpose Word lift Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean#L244-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean#L244-L247

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
open PI.WGL.Fock6

theorem PI.WGL.Fock6.transposeWord_liftWord {n N : ℕ} (h : n + 1 = N) (w : List (Fin n × Fin n × ℕ)) :
    transposeWord (liftWord h w) = liftWord h (transposeWord w) := by sorry
