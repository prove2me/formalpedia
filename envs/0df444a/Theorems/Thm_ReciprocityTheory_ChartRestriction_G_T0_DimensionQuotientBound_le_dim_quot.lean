-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_DimensionQuotientBound_le_dim_quot
-- name    : ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound.le_dim_quot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:39.654158+00:00
-- url     : https://prove2.me/theorems/f214f758-e908-58b0-97b4-52064787179d
-- title:
--   Dimension Quotient Bound: le dim quot
-- statement:
--   The Dimension Quotient Bound construction uses the le dim quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DimensionQuotientBound.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DimensionQuotientBound.lean#L7-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AvPrimeDimOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DimensionQuotientBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound
open IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound.le_dim_quot {R : Type*} [CommRing R] (p P m : Ideal R) [hp : p.IsPrime] [hP : P.IsPrime]
    [hm : m.IsPrime] (h1 : p < P) (h2 : P < m) : (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by sorry
