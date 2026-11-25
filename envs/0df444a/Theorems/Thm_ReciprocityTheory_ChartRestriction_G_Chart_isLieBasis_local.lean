-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieBasis_local
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_local
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:57.990045+00:00
-- url     : https://prove2.me/theorems/a4a80146-463d-5b76-bde2-430286e63bae
-- title:
--   Chart: is Lie Basis local
-- statement:
--   The Chart construction uses the is Lie Basis local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean#L155-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean#L155-L180

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
variable (p : Ideal S) [p.IsPrime]
variable [∀ s : S, Smooth (Gs G s).hom]

theorem ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_local {d : ℕ} {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u) :
    Geo.Tor.IsLieBasis (G := Gp (G := G) p) (fun i => resP p (u i)) := by sorry
