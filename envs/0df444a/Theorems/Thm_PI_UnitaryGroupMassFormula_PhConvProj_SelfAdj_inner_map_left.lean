-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_SelfAdj_inner_map_left
-- name    : PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.inner_map_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:32:56.298041+00:00
-- url     : https://prove2.me/theorems/5e7b4da7-cde7-4627-abd1-950445d7497a
-- title:
--   Self Adj: inner map left
-- statement:
--   The Self Adj construction uses the inner map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/SelfAdj.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/SelfAdj.lean#L29-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhConvProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_SelfAdj
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhConvProj PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
open PI.PhConvProj
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.inner_map_left {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (x y : K) :
    ⟪π g x, y⟫_ℂ = ⟪x, π g⁻¹ y⟫_ℂ := by sorry
