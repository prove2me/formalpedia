-- Prove2me | Theorems.Thm_PI_UD_eval_bind_leftSubst
-- name    : PI.UD.eval_bind_leftSubst
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:27.415829+00:00
-- url     : https://prove2.me/theorems/256f1faa-8668-4c76-b1d3-b35e7976327a
-- title:
--   UD: eval bind left Subst
-- statement:
--   The UD construction uses the eval bind left Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/EvalBindTorusSubst.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/EvalBindTorusSubst.lean#L42-L48

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

theorem PI.UD.eval_bind_leftSubst {ι : Type} {n : ℕ} (A : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (u : ι → Matrix (Fin n) (Fin n) ℂ) :
    eval (fun x : ι × Fin n × Fin n => u x.1 x.2.1 x.2.2) (bind₁ (leftSubst A) P) =
      eval (fun x : ι × Fin n × Fin n => (A x.1 * u x.1) x.2.1 x.2.2) P := by sorry
