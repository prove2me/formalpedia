-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fromSpec_appLE_top
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.fromSpec_appLE_top
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:02.859705+00:00
-- url     : https://prove2.me/theorems/fd7fda6a-0ceb-51ca-94a3-7ac8116bb5c0
-- title:
--   DVR: from Spec app LE top
-- statement:
--   The DVR construction uses the from Spec app LE top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L16-L20

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.fromSpec_appLE_top {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by sorry
