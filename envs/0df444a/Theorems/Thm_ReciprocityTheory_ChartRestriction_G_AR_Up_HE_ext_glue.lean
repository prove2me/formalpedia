-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_ext_glue
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.HE.ext_glue
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:21:03.545417+00:00
-- url     : https://prove2.me/theorems/9b1a0790-1f92-4bcc-ba36-78ccec28ebef
-- title:
--   HE: ext glue
-- statement:
--   The HE construction uses the ext glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/InterpStatementPfD.lean#L12-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/InterpStatementPfD.lean#L12-L58

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.HE
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal
noncomputable section
variable {n : ℕ} {U : Set (V n)}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.HE.ext_glue (hU : IsOpen U) (g G : V n → ℂ) (hg : DifferentiableOn ℂ g U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0)
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ g y ≠ 0})
    (hL : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | g y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ g y ≠ 0} := by sorry
