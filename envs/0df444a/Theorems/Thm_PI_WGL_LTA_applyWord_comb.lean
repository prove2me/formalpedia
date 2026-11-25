-- Prove2me | Theorems.Thm_PI_WGL_LTA_applyWord_comb
-- name    : PI.WGL.LTA.applyWord_comb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:58:05.912579+00:00
-- url     : https://prove2.me/theorems/d9e1709e-221e-5011-aa03-5d902dbd42c5
-- title:
--   LTA: apply Word comb
-- statement:
--   The LTA construction uses the apply Word comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleA.lean#L245-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleA.lean#L245-L260

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTA
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WGL.LTA.applyWord_comb {r c n K : ℕ} (e : Fin n → Fin r) (sz : Fin K → ℕ)
    (G : ∀ k, (Fin (sz k) → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) (hG : ∀ k, Exp e (G k))
    (C0 : MvPolynomial (Fin r × Fin c) ℤ)
    (hC : ∀ a b : Fin n, a ≠ b → rowGen ℤ (e a) (e b) C0 = Polynomial.C C0) :
    ∀ (w : List (Fin n × Fin n × ℕ)), OffDiag w → ∀ d,
      applyWord ℤ (w.map fun x => (e x.1, e x.2.1, x.2.2))
        (Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) d) =
      Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) (twd sz w d)
  := by sorry
