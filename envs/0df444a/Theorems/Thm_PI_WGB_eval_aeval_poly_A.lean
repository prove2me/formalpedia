-- Prove2me | Theorems.Thm_PI_WGB_eval_aeval_poly_A
-- name    : PI.WGB.eval_aeval_poly_A
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:47:00.838652+00:00
-- url     : https://prove2.me/theorems/7a37dce2-eed4-4d0c-ab9c-f23c365231c0
-- title:
--   WGB: eval aeval poly A
-- statement:
--   The WGB construction uses the eval aeval poly A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FixedLineProofA.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FixedLineProofA.lean#L12-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FixedLineProofA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}

theorem PI.WGB.eval_aeval_poly_A {σ : Type*} (Y : σ → Polynomial ℂ) (f : MvPolynomial σ ℂ) (e : ℂ) :
    (aeval Y f).eval e = eval (fun v => (Y v).eval e) f := by sorry
