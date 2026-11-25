-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_Sand_urep_inner
-- name    : PI.UnitaryGroupMassFormula.PhConvProj.Sand.urep_inner
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:32:44.821226+00:00
-- url     : https://prove2.me/theorems/8ac3d04c-8a65-4659-87e8-6aca92d13d0c
-- title:
--   Sand: urep inner
-- statement:
--   The Sand construction uses the urep inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/UrepMulApply.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/UrepMulApply.lean#L18-L21

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

theorem PI.UnitaryGroupMassFormula.PhConvProj.Sand.urep_inner {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (k : G) (u v : K) :
    ⟪π k u, π k v⟫_ℂ = ⟪u, v⟫_ℂ := by sorry
