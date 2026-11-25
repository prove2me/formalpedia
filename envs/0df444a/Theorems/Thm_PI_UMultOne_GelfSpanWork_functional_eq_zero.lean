-- Prove2me | Theorems.Thm_PI_UMultOne_GelfSpanWork_functional_eq_zero
-- name    : PI.UMultOne.GelfSpanWork.functional_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:29:23.555302+00:00
-- url     : https://prove2.me/theorems/c25bc265-6bac-4ae4-88c2-bb97a851662f
-- title:
--   Gelf Span Work: functional eq zero
-- statement:
--   The Gelf Span Work construction uses the functional eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L113-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L113-L133

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralSpanAlgebra_Burnside
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.GelfSpanWork
open Matrix Module
variable {G : Type} [Group G] {N : ℕ}

theorem PI.UMultOne.GelfSpanWork.functional_eq_zero (ρ : G →* GL (Fin N) ℂ) (hI : Irr ρ)
    (ℓ : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ g, ℓ ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 0) : ℓ = 0 := by sorry
