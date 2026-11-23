-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_SelfAdj_inner_map_map
-- name    : PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.inner_map_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:49.6069+00:00
-- url     : https://prove2.me/theorems/ac3bda24-0268-414c-ad7d-834681e28beb
-- title:
--   Self Adj: inner map map
-- statement:
--   The Self Adj construction uses the inner map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/SelfAdj.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/SelfAdj.lean#L17-L20

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

theorem PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.inner_map_map {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (x y : K) :
    ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := by sorry
