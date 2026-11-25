-- Prove2me | Theorems.Thm_PI_UMultOne_GelfSpanWork_spanAlg_toSubmodule
-- name    : PI.UMultOne.GelfSpanWork.spanAlg_toSubmodule
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:14.662006+00:00
-- url     : https://prove2.me/theorems/248fa173-c223-4c89-82a4-6e5aee53349d
-- title:
--   Gelf Span Work: span Alg to Submodule
-- statement:
--   The Gelf Span Work construction uses the span Alg to Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L32-L36

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

theorem PI.UMultOne.GelfSpanWork.spanAlg_toSubmodule (ρ : G →* GL (Fin N) ℂ) :
    Subalgebra.toSubmodule (spanAlg ρ) = Submodule.span ℂ (Set.range (repEnd ρ)) := by sorry
