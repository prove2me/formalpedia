-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_exists_int_multiple
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.exists_int_multiple
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:42:43.279446+00:00
-- url     : https://prove2.me/theorems/3b22e144-5d05-519f-8cdf-82120c5d6a09
-- title:
--   Satake Vectors: exists int multiple
-- statement:
--   The Satake Vectors construction uses the exists int multiple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L322-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L322-L344

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.exists_int_multiple {κ : Type} (F : MvPolynomial κ K) :
    ∃ (c : K) (G₀ : MvPolynomial κ (𝓞 K)), c ≠ 0 ∧
      MvPolynomial.map (algebraMap (𝓞 K) K) G₀ = MvPolynomial.C c * F := by sorry
