-- Prove2me | Theorems.Thm_PI_WGB_eval_lpMinor_one
-- name    : PI.WGB.eval_lpMinor_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:45:34.241284+00:00
-- url     : https://prove2.me/theorems/96a38220-11fe-479d-991b-fa37fe16925d
-- title:
--   WGB: eval lp Minor one
-- statement:
--   The WGB construction uses the eval lp Minor one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L202-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L202-L209

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
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
variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)
variable {f}

theorem PI.WGB.eval_lpMinor_one (s : ℕ) (h1 h2 : s ≤ n) :
    eval (fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2) (lpMinor ℂ s h1 h2) = 1 := by sorry
