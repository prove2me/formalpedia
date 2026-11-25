-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_CanonicalLiftUnpacking_exists_zero_qk
-- name    : ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking.exists_zero_qk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:58.570795+00:00
-- url     : https://prove2.me/theorems/d0058cf6-9d4d-4291-9984-98f8c4fc7d1d
-- title:
--   Canonical Lift Unpacking: exists zero qk
-- statement:
--   The Canonical Lift Unpacking construction uses the exists zero qk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/CanonicalLiftUnpacking.lean#L21-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/CanonicalLiftUnpacking.lean#L21-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_CanonicalLiftUnpacking
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking.exists_zero_qk (hB : D.TauBimult) (k : ℕ) :
    ∃ p0 : QkPt D F k, p0.y = 0 ∧ p0.g.IsZero ∧ p0.g.IsAdd p0.g p0.g := by sorry
