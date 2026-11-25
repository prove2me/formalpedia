-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExG_isCompact_sub
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ExG.isCompact_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:13.076464+00:00
-- url     : https://prove2.me/theorems/fcf3cbfa-6e55-5d21-8684-5cfedcbd63c5
-- title:
--   Ex G: is Compact sub
-- statement:
--   The Ex G construction uses the is Compact sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustGPf.lean#L61-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustGPf.lean#L61-L95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPf
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustGPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhC_isCompact_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.FD
open scoped ContDiff
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.AR.Up.ExG
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ExG.isCompact_sub (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (g1 : V (nd X) → ℂ)
    (hg : DifferentiableOn ℂ g1 (OmF X x0)) (a : ℝ) :
    IsCompact {z : V (nd X) | (z ∈ OmF X x0 ∧ g1 z ≠ 0) ∧ eF X x0 z + (‖g1 z‖ ^ 2)⁻¹ ≤ a} := by sorry
