-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_frameLieBC
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.frameLieBC
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:41.137918+00:00
-- url     : https://prove2.me/theorems/ae011d0f-34dc-574c-bb51-375d1863476e
-- title:
--   Chart: frame Lie BC
-- statement:
--   The Chart construction uses the frame Lie BC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean#L184-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean#L184-L233

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem ReciprocityTheory.ChartRestriction.G.Chart.frameLieBC {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G] [Smooth G.hom] {d : ℕ}
    {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u) {k : Type} [Field k] (φ : S →+* k)
    {G' : Over (Spec (CommRingCat.of k))} [GrpObj G'] {F : G'.left ⟶ G.left}
    (h : Geo.Tor.IsGrpPullback G' G (Geo.Tor.spMap φ) F) {u' : Fin d → (Geo.Tor.epsR k ⟶ G')}
    (hu' : ∀ i, (u' i).left ≫ F = Geo.Tor.spMap (dualMapR φ) ≫ (u i).left) : Geo.Tor.IsLieBasis u' := by sorry
