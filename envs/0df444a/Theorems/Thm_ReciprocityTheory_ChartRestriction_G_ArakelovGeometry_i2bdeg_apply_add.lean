-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2bdeg_apply_add
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2bdeg_apply_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:10.581566+00:00
-- url     : https://prove2.me/theorems/2c3fe143-8971-4a87-bdab-f271ee59ed67
-- title:
--   Arakelov Geometry: i2bdeg apply add
-- statement:
--   The Arakelov Geometry construction uses the i2bdeg apply add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L125-L127

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2bdeg_apply_add (m n : (Σ k, ι k) →₀ ℕ) (k : K) :
    i2bdeg (m + n) k = i2bdeg m k + i2bdeg n k := by sorry
