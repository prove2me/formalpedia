-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_map_of_app_fst_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.mem_map_of_app_fst_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:29.254797+00:00
-- url     : https://prove2.me/theorems/8864b47f-f13f-5bb3-95b2-0438a3254e30
-- title:
--   DVR: mem map of app fst eq zero
-- statement:
--   The DVR construction uses the mem map of app fst eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L25-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L25-L89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [CommRing V] {X : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.DVR.mem_map_of_app_fst_eq_zero (p : X ⟶ Sp V) (J : Ideal V) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U))
    (ha : ((pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).app U).hom a = 0) :
    a ∈ J.map (strMap p U) := by sorry
