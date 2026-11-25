-- Prove2me | Theorems.Thm_PI_UD_eq_zero_of_torus
-- name    : PI.UD.eq_zero_of_torus
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:37.456604+00:00
-- url     : https://prove2.me/theorems/472c1257-e645-4fb3-85af-39e1332f5088
-- title:
--   UD: eq zero of torus
-- statement:
--   The UD construction uses the eq zero of torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/EvalBindTorusSubst.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/EvalBindTorusSubst.lean#L19-L22

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

theorem PI.UD.eq_zero_of_torus {σ : Type*} (R : MvPolynomial σ ℂ)
    (h : ∀ t : σ → ℂ, (∀ i, ‖t i‖ = 1) → eval t R = 0) : R = 0 := by sorry
