-- Prove2me | Theorems.Thm_PI_WGL_Fock6_rowDiv_diag
-- name    : PI.WGL.Fock6.rowDiv_diag
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:06.552113+00:00
-- url     : https://prove2.me/theorems/b3057d8b-7fa6-474f-bf6f-570bde48ad2a
-- title:
--   Fock6: row Div diag
-- statement:
--   The Fock6 construction uses the row Div diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean#L71-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean#L71-L84

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

theorem PI.WGL.Fock6.rowDiv_diag {r n : ℕ} (a : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℂ) (H : ℤ)
    (hf : IsWeightedHomogeneous (rw1 a) f H) :
    rowDiv ℂ a a k f = ((H.toNat.choose k : ℕ) : ℂ) • f := by sorry
