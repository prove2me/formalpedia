-- Prove2me | Theorems.Thm_PI_WGL_Fock6_weight_rw1_eq_weight_wa
-- name    : PI.WGL.Fock6.weight_rw1_eq_weight_wa
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:46:12.489948+00:00
-- url     : https://prove2.me/theorems/134c88e3-19fd-479d-803f-23550d25ffe8
-- title:
--   Fock6: weight rw1 eq weight wa
-- statement:
--   The Fock6 construction uses the weight rw1 eq weight wa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean#L38-L43

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

theorem PI.WGL.Fock6.weight_rw1_eq_weight_wa {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (c : Fin r) :
    Finsupp.weight (rw1 c) m = ((Finsupp.weight (wa c) m : ℕ) : ℤ) := by sorry
