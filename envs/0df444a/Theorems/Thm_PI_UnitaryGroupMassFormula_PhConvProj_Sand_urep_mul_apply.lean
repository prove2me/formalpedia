-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_Sand_urep_mul_apply
-- name    : PI.UnitaryGroupMassFormula.PhConvProj.Sand.urep_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:56.740479+00:00
-- url     : https://prove2.me/theorems/7a03a9c5-1210-40d9-b73a-122f385afb81
-- title:
--   Sand: urep mul apply
-- statement:
--   The Sand construction uses the urep mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/UrepMulApply.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/UrepMulApply.lean#L23-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_UrepMulApply
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhConvProj PI.UnitaryGroupMassFormula.PhConvProj.Sand
open PI.PhConvProj
variable {G : Type} [Group G] [TopologicalSpace G] {K : Type} [NormedAddCommGroup K]
  [InnerProductSpace ℂ K]

theorem PI.UnitaryGroupMassFormula.PhConvProj.Sand.urep_mul_apply {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (a b : G) (v : K) :
    π (a * b) v = π a (π b v) := by sorry
