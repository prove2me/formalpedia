-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2comp_mul_right
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2comp_mul_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:58.715606+00:00
-- url     : https://prove2.me/theorems/00e72c46-1a41-4550-a693-98ac38bd63ac
-- title:
--   Arakelov Geometry: i2comp mul right
-- statement:
--   The Arakelov Geometry construction uses the i2comp mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L130-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L130-L185

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2comp_mul_right {f : MRing ι} {c : K → ℕ} (hf : IsMultiHomog f c) (a : K → ℕ)
    (g : MRing ι) : i2comp a (g * f) = if c ≤ a then i2comp (a - c) g * f else 0 := by sorry
