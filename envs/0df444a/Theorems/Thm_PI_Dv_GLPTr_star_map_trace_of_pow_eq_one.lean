-- Prove2me | Theorems.Thm_PI_Dv_GLPTr_star_map_trace_of_pow_eq_one
-- name    : PI.Dv.GLPTr.star_map_trace_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:01.581838+00:00
-- url     : https://prove2.me/theorems/97a86c89-bf5a-54a3-8379-bc6e5ff480e7
-- title:
--   GLPTr: star map trace of pow eq one
-- statement:
--   The GLPTr construction uses the star map trace of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/StarMapTraceOfPowEqOne.lean#L47-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/StarMapTraceOfPowEqOne.lean#L47-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_StarMapTraceOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLPTr
open Matrix
open scoped ComplexOrder

theorem PI.Dv.GLPTr.star_map_trace_of_pow_eq_one {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (σ : K →+* ℂ) (f : Module.End K W) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) :
    star (σ (LinearMap.trace K W f)) = σ (LinearMap.trace K W (f ^ (n - 1))) := by sorry
