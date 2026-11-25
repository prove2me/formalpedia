-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_Sand_urep_adj
-- name    : PI.UnitaryGroupMassFormula.PhConvProj.Sand.urep_adj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:33:03.706015+00:00
-- url     : https://prove2.me/theorems/7d2da5d8-429e-48e8-8551-6cd23b529e13
-- title:
--   Sand: urep adj
-- statement:
--   The Sand construction uses the urep adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/UrepMulApply.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/UrepMulApply.lean#L28-L33

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

theorem PI.UnitaryGroupMassFormula.PhConvProj.Sand.urep_adj {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (k : G) (u v : K) :
    ⟪π k u, v⟫_ℂ = ⟪u, π k⁻¹ v⟫_ℂ := by sorry
