-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2comp_mem
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2comp_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:09:49.889248+00:00
-- url     : https://prove2.me/theorems/d1872e26-fcb3-5db6-ac16-681b1bd18d6a
-- title:
--   Arakelov Geometry: i2comp mem
-- statement:
--   The Arakelov Geometry construction uses the i2comp mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L188-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L188-L213

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
open Classical

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2comp_mem {F : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) (a : K → ℕ) {u : MRing ι}
    (hu : u ∈ F) : i2comp a u ∈ F := by sorry
