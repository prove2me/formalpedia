-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_inner_le
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.FM.inner_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:27.026374+00:00
-- url     : https://prove2.me/theorems/da40c2d3-243b-54f2-8530-06698d9913dc
-- title:
--   FM: inner le
-- statement:
--   The FM construction uses the inner le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfC.lean#L138-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfC.lean#L138-L178

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
attribute [local instance] haarF haarIx

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.FM.inner_le {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C)
    (hCd : C ⊆ X.dom) {R0 : ℝ} (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0)
    {G : Frame X.Ψ r → ℝ≥0∞} (hGinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x)
    (x : LoI X.Ψ r → ℂ) :
    ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then ENNReal.ofReal (Complex.normSq (jacU y)) *
      C.indicator G (ufC X (LA (fun τ => mat x0 τ) (lu ((eS X.Ψ r).symm (x, y))))) else 0) ≤
      KR X R0 * GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x := by sorry
