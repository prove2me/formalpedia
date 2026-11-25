-- Prove2me | Theorems.Thm_PI_UMultOne_GelfSpanWork_spanAlg_simple
-- name    : PI.UMultOne.GelfSpanWork.spanAlg_simple
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:39.465983+00:00
-- url     : https://prove2.me/theorems/6510a41f-b2b6-4844-b57b-8f94ea9ddf92
-- title:
--   Gelf Span Work: span Alg simple
-- statement:
--   The Gelf Span Work construction uses the span Alg simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L41-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSpanAlgebra/Burnside.lean#L41-L61

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

theorem PI.UMultOne.GelfSpanWork.spanAlg_simple (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ) :
    IsSimpleModule (spanAlg ρ) (Fin N → ℂ) := by sorry
