-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_height_pow_multiHomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.T0.height_pow_multiHomogeneous
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:46:39.196157+00:00
-- url     : https://prove2.me/theorems/b2b3dc4b-abd2-409c-9dfb-29a41b760913
-- title:
--   T0: height pow multi Homogeneous
-- statement:
--   The T0 construction uses the height pow multi Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightProdPowMultiHomogeneous.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightProdPowMultiHomogeneous.lean#L35-L46

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

theorem ReciprocityTheory.ChartRestriction.G.T0.height_pow_multiHomogeneous {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n)
    {g : MvPolynomial (Fin B × Fin n) K} {a : Fin B → ℕ} (hg0 : g ≠ 0)
    (hg : IsMultiHomogeneous a g) (e : ℕ) :
    g ^ e ≠ 0 ∧ IsMultiHomogeneous (e • a) (g ^ e) ∧ h0 (g ^ e) = e * h0 g := by sorry
