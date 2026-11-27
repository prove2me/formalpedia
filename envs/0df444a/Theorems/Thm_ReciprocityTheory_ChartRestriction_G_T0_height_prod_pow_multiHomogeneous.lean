-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_height_prod_pow_multiHomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.T0.height_prod_pow_multiHomogeneous
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:39:09.256958+00:00
-- url     : https://prove2.me/theorems/fa40897c-fb9a-5973-9db1-99c7e6699a69
-- title:
--   T0: height prod pow multi Homogeneous
-- statement:
--   The T0 construction uses the height prod pow multi Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightProdPowMultiHomogeneous.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightProdPowMultiHomogeneous.lean#L48-L62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationGenericRatioEqRestriction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightProdPowMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField ReciprocityTheory.MultiplicativeHeights

theorem ReciprocityTheory.ChartRestriction.G.T0.height_prod_pow_multiHomogeneous {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) {ι' : Type*}
    (T : Finset ι') (g : ι' → MvPolynomial (Fin B × Fin n) K) (e : ι' → ℕ)
    (hg : ∀ i ∈ T, g i ≠ 0 ∧ ∃ a, IsMultiHomogeneous a (g i)) :
    (∏ i ∈ T, g i ^ e i) ≠ 0 ∧ (∃ a, IsMultiHomogeneous a (∏ i ∈ T, g i ^ e i)) ∧
      h0 (∏ i ∈ T, g i ^ e i) = ∑ i ∈ T, (e i : ℝ) * h0 (g i) := by sorry
