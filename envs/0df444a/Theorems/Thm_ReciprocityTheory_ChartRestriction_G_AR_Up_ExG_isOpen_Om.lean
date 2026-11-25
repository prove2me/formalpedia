-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExG_isOpen_Om
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ExG.isOpen_Om
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:58:45.062666+00:00
-- url     : https://prove2.me/theorems/31d77974-187a-5691-a6ad-43eb48c8fae7
-- title:
--   Ex G: is Open Om
-- statement:
--   The Ex G construction uses the is Open Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustGPf.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustGPf.lean#L34-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPf
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustGPf
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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ExG.isOpen_Om (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0)) :
    IsOpen {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := by sorry
