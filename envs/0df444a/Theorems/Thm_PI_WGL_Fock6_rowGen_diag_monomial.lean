-- Prove2me | Theorems.Thm_PI_WGL_Fock6_rowGen_diag_monomial
-- name    : PI.WGL.Fock6.rowGen_diag_monomial
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:00:37.678422+00:00
-- url     : https://prove2.me/theorems/d4e8e654-f17f-59fd-b55f-ddf8c5688aea
-- title:
--   Fock6: row Gen diag monomial
-- statement:
--   The Fock6 construction uses the row Gen diag monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean#L60-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftFock.lean#L60-L69

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

theorem PI.WGL.Fock6.rowGen_diag_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    rowGen ℂ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (wa a) m) := by sorry
