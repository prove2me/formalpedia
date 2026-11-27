-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_not_dim_strict_lt_bound
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.not_dim_strict_lt_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:12:26.080076+00:00
-- url     : https://prove2.me/theorems/9ab64ec5-36ef-48c2-98b6-61aaa02116db
-- title:
--   Arakelov Geometry: not dim strict lt bound
-- statement:
--   The Arakelov Geometry construction uses the not dim strict lt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean#L56-L63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime
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
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.not_dim_strict_lt_bound {x y : WithBot ℕ∞} {D : ℕ} (hx : x = ((D + 2 : ℕ) : WithBot ℕ∞))
    (h : x + 1 ≤ y) (hy : y ≤ ((D + 2 : ℕ) : WithBot ℕ∞)) : False := by sorry
