-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhSchurConv_Main_map_mul_apply
-- name    : PI.UnitaryGroupMassFormula.PhSchurConv.Main.map_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:45:59.191781+00:00
-- url     : https://prove2.me/theorems/1f287673-86f9-49da-822a-9acc38ee7ee7
-- title:
--   Main: map mul apply
-- statement:
--   The Main construction uses the map mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurConvolution/MapMulApply.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurConvolution/MapMulApply.lean#L17-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhSchurConv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurConvolution_MapMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhSchurConv PI.UnitaryGroupMassFormula.PhSchurConv.Main
open PI.PhSchurConv

theorem PI.UnitaryGroupMassFormula.PhSchurConv.Main.map_mul_apply {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (a b : G) (v : H) : σ (a * b) v = σ a (σ b v) := by sorry
