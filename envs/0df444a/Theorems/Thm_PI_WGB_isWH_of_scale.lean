-- Prove2me | Theorems.Thm_PI_WGB_isWH_of_scale
-- name    : PI.WGB.isWH_of_scale
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:58.012915+00:00
-- url     : https://prove2.me/theorems/ba8a7ea5-0261-5553-a3b0-6cb20dcf07c1
-- title:
--   WGB: is WH of scale
-- statement:
--   The WGB construction uses the is WH of scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L175-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L175-L200

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

theorem PI.WGB.isWH_of_scale (κ : Fin n → ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (h : ∀ t : Fin n → ℂˣ, aeval (fun v : Fin n × Fin n => C ((t v.2 : ℂ)) * X v) P =
      C (∏ i, (t i : ℂ) ^ κ i) * P) :
    IsWeightedHomogeneous (colW n n) P κ := by sorry
