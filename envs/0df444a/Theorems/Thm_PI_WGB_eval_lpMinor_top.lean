-- Prove2me | Theorems.Thm_PI_WGB_eval_lpMinor_top
-- name    : PI.WGB.eval_lpMinor_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:45:42.150821+00:00
-- url     : https://prove2.me/theorems/e0109abb-e177-433a-be50-2601562bae8f
-- title:
--   WGB: eval lp Minor top
-- statement:
--   The WGB construction uses the eval lp Minor top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/TransposeConjComm.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/TransposeConjComm.lean#L27-L33

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
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
open Formalism.REAL (fockF)

theorem PI.WGB.eval_lpMinor_top {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℕ) (h1 h2 : s ≤ n) (hs : s = n) :
    eval (fun v : Fin n × Fin n => Z v.1 v.2) (lpMinor ℂ s h1 h2) = Z.det := by sorry
