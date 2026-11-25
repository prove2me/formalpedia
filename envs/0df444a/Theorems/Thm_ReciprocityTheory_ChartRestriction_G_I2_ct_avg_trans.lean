-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_avg_trans
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_avg_trans
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:29:30.400802+00:00
-- url     : https://prove2.me/theorems/a2847336-1f01-44ef-8de6-2c855b7aba1e
-- title:
--   I2: ct avg trans
-- statement:
--   The I2 construction uses the ct avg trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusC.lean#L173-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusC.lean#L173-L193

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_avg_trans (Y : GT ι) (g : EuclideanSpace ℂ ι → ℝ)
    (hper : ∀ γ ∈ lat Y.b, ∀ v, g (v + γ) = g v) (a : EuclideanSpace ℂ ι) :
    (⨍ v in ZSpan.fundamentalDomain Y.b, g (v - a)) = ⨍ v in ZSpan.fundamentalDomain Y.b, g v := by sorry
