-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_nat_of_two_le_dim_le
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_of_two_le_dim_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:12:13.637262+00:00
-- url     : https://prove2.me/theorems/681002b8-9198-4a1c-86d5-46efc8625e1b
-- title:
--   Arakelov Geometry: exists nat of two le dim le
-- statement:
--   The Arakelov Geometry construction uses the exists nat of two le dim le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean#L40-L54

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_of_two_le_dim_le {x : WithBot ℕ∞} {D : ℕ} (h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ x)
    (hD : x ≤ ((D + 2 : ℕ) : WithBot ℕ∞)) : ∃ d ≤ D, x = ((d + 2 : ℕ) : WithBot ℕ∞) := by sorry
