-- Prove2me | Theorems.Thm_PI_UMultOne_GelfSpanWork_spanAlg_eq_top
-- name    : PI.UMultOne.GelfSpanWork.spanAlg_eq_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:16.155799+00:00
-- url     : https://prove2.me/theorems/3d4a3179-d2a8-45d1-9b5d-d080c56fe379
-- title:
--   Gelf Span Work: span Alg eq top
-- statement:
--   The Gelf Span Work construction uses the span Alg eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L93-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L93-L111

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

theorem PI.UMultOne.GelfSpanWork.spanAlg_eq_top (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ) :
    ∀ f : Module.End ℂ (Fin N → ℂ), f ∈ spanAlg ρ := by sorry
