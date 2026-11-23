-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_abLocus_pullback
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus_pullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:14.206593+00:00
-- url     : https://prove2.me/theorems/ca49b62e-4ba0-483f-b11f-8ad1d2489dc2
-- title:
--   Tor: ab Locus pullback
-- statement:
--   The Tor construction uses the ab Locus pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/OneArc.lean#L34-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/OneArc.lean#L34-L72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus_pullback (hA : AbLocusOneSt) {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G]
    (hG : IsSemiAbelian G) {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f) (x : S') :
    f x ∈ abLocus G ↔ x ∈ abLocus G' := by sorry
