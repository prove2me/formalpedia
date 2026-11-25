-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paTh_sec
-- name    : ReciprocityTheory.ChartRestriction.G.I2.paTh_sec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:33.716526+00:00
-- url     : https://prove2.me/theorems/f00c891a-8e36-5614-9678-dbe2e0396562
-- title:
--   I2: pa Th sec
-- statement:
--   The I2 construction uses the pa Th sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L274-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L274-L295

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.paTh_sec (Y : GT ι) {q : ℕ}
    (hC : ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
      Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I))
    {F : EuclideanSpace ℂ ι → ℂ} (hd : Differentiable ℂ (paTh Y q F))
    (hs : ∀ v, Summable (fun γ : lat Y.b => Y.ka γ * paU q γ F v)) :
    paTh Y q F ∈ Y.Sec q := by sorry
