-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_re_star_dotProduct_mulVec_1cf65725569f
-- name    : P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_re_star_dotProduct_mulVec_1cf65725569f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:00.59407+00:00
-- url     : https://prove2.me/theorems/64630670-3e06-457d-a38d-102e91395e72
-- title:
--   P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt re star dot Product mul Vec 1cf65725569f: P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt re star dot Product mul Vec 1cf6
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt re star dot Product mul Vec 1cf65725569f construction uses the P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt re star dot Product mul Vec 1cf65725569f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineSemipositive.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineSemipositive.lean#L26-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualLineSemipositiveAlt

theorem P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_re_star_dotProduct_mulVec_1cf65725569f {n : Type} [Fintype n] (B : Matrix n n ℂ) (w : n → ℂ) :
    (star w ⬝ᵥ ((Bᴴ * B) *ᵥ w)).re = ∑ j, ‖(B *ᵥ w) j‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualLineSemipositiveAlt».«re_star_dotProduct_mulVec» := P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_re_star_dotProduct_mulVec_1cf65725569f
