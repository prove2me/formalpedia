-- Prove2me | Theorems.Thm_PI_WGB_aeval_scale_monomial
-- name    : PI.WGB.aeval_scale_monomial
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:47.050155+00:00
-- url     : https://prove2.me/theorems/4588ce06-3c90-410e-a76b-14c1ed5287af
-- title:
--   WGB: aeval scale monomial
-- statement:
--   The WGB construction uses the aeval scale monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L155-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L155-L162

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

theorem PI.WGB.aeval_scale_monomial (t : Fin n → ℂ) (m : Fin n × Fin n →₀ ℕ) (a : ℂ) :
    aeval (fun v : Fin n × Fin n => C (t v.2) * X v) (monomial m a) =
      monomial m (a * m.prod fun v e => t v.2 ^ e) := by sorry
