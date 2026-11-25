-- Prove2me | Theorems.Thm_PI_Dv_GLPTr_star_map_trace_rep
-- name    : PI.Dv.GLPTr.star_map_trace_rep
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:12.293059+00:00
-- url     : https://prove2.me/theorems/1ef92113-60b3-4820-a5a8-a189963982f2
-- title:
--   GLPTr: star map trace rep
-- statement:
--   The GLPTr construction uses the star map trace rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/StarMapTraceOfPowEqOne.lean#L64-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/StarMapTraceOfPowEqOne.lean#L64-L74

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

theorem PI.Dv.GLPTr.star_map_trace_rep {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (σ : K →+* ℂ)
    (τ : Representation K G W) (g : G) :
    star (σ (LinearMap.trace K W (τ g))) = σ (LinearMap.trace K W (τ g⁻¹)) := by sorry
