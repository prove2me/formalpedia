-- Prove2me | Theorems.Thm_PI_WGB_eval_aeval_self
-- name    : PI.WGB.eval_aeval_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:38.356254+00:00
-- url     : https://prove2.me/theorems/d94ef386-5bee-4aec-83ba-663b9f093e0a
-- title:
--   WGB: eval aeval self
-- statement:
--   The WGB construction uses the eval aeval self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L39-L41

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

theorem PI.WGB.eval_aeval_self {σ : Type} (x : σ → ℂ) (g : σ → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ) :
    eval x (aeval g p) = eval (fun v => eval x (g v)) p := by sorry
