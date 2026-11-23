-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhSchurConv_Main_inner_map
-- name    : PI.UnitaryGroupMassFormula.PhSchurConv.Main.inner_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:45:57.721744+00:00
-- url     : https://prove2.me/theorems/86b68414-fb4c-44d8-91e6-2876ec518eab
-- title:
--   Main: inner map
-- statement:
--   The Main construction uses the inner map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurConvolution/MapMulApply.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurConvolution/MapMulApply.lean#L23-L27

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

theorem PI.UnitaryGroupMassFormula.PhSchurConv.Main.inner_map {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g : G) (a b : H) : ⟪σ g a, σ g b⟫_ℂ = ⟪a, b⟫_ℂ := by sorry
