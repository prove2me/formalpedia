-- Prove2me | Theorems.Thm_PI_WGL_LTE_Mlift_mem_colWt
-- name    : PI.WGL.LTE.Mlift_mem_colWt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:57:51.358989+00:00
-- url     : https://prove2.me/theorems/bcf13ef5-b338-5a27-8d9b-fd79b1d03096
-- title:
--   LTE: Mlift mem col Wt
-- statement:
--   The LTE construction uses the Mlift mem col Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleE.lean#L75-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleE.lean#L75-L90

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD

theorem PI.WGL.LTE.Mlift_mem_colWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ}
    (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n) :
    Mlift h lam sg sz hsz L I ∈ dualWeyl ℤ N N (colWt h lam sg sz L) := by sorry
