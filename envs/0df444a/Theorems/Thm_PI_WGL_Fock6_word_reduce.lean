-- Prove2me | Theorems.Thm_PI_WGL_Fock6_word_reduce
-- name    : PI.WGL.Fock6.word_reduce
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:46:25.54535+00:00
-- url     : https://prove2.me/theorems/87303f45-2f00-45d7-9f93-0c5da0c78906
-- title:
--   Fock6: word reduce
-- statement:
--   The Fock6 construction uses the word reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean#L199-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean#L199-L224

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

theorem PI.WGL.Fock6.word_reduce {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hf : ∀ c : Fin r, ∃ H : ℤ, IsWeightedHomogeneous (rw1 c) f H) (w : List (Fin r × Fin r × ℕ)) :
    ∃ w', OffDiag w' ∧ ∃ z : ℂ, applyWord ℂ w f = z • applyWord ℂ w' f := by sorry
