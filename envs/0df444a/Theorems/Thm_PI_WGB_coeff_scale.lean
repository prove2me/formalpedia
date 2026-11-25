-- Prove2me | Theorems.Thm_PI_WGB_coeff_scale
-- name    : PI.WGB.coeff_scale
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:50:11.898486+00:00
-- url     : https://prove2.me/theorems/066de988-542a-59fc-b5c4-50fa2a26c35e
-- title:
--   WGB: coeff scale
-- statement:
--   The WGB construction uses the coeff scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L164-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L164-L173

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

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

theorem PI.WGB.coeff_scale (t : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) (m : Fin n × Fin n →₀ ℕ) :
    coeff m (aeval (fun v : Fin n × Fin n => C (t v.2) * X v) P) = (m.prod fun v e => t v.2 ^ e) * coeff m P := by sorry
