-- Prove2me | Theorems.Thm_PI_UD_eval_bind_torusSubst
-- name    : PI.UD.eval_bind_torusSubst
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:41.300967+00:00
-- url     : https://prove2.me/theorems/f1f072cf-5985-4292-9f49-ce71e3cfc22c
-- title:
--   UD: eval bind torus Subst
-- statement:
--   The UD construction uses the eval bind torus Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/EvalBindTorusSubst.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/EvalBindTorusSubst.lean#L28-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_GramStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UD

theorem PI.UD.eval_bind_torusSubst {ι : Type} {n : ℕ} (w v : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (t : ι × Fin n → ℂ) :
    eval t (bind₁ (torusSubst w v) P) =
      eval (fun x : ι × Fin n × Fin n =>
        (w x.1 * diagonal (fun k => t (x.1, k)) * v x.1) x.2.1 x.2.2) P := by sorry
