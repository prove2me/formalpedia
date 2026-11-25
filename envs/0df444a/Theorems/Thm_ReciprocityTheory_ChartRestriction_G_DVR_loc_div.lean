-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_loc_div
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.loc_div
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:45.340396+00:00
-- url     : https://prove2.me/theorems/b4ede6b2-72ad-5ac8-99da-e67ee88ebb42
-- title:
--   DVR: loc div
-- statement:
--   The DVR construction uses the loc div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L91-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L91-L112

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.loc_div {P : Scheme.{0}} (p' : P ⟶ Sp V) (W : P.Opens) (f : Γ(P, W)) (r : V) (x : P) (hx : x ∈ W)
    (h : cst p' x r ∣ gs (𝟙 P) x W f) : ∃ (U : P.Opens) (_ : U ≤ W) (_ : x ∈ U) (g : Γ(P, U)),
      ∀ y ∈ U, gs (𝟙 P) y W f = cst p' y r * gs (𝟙 P) y U g := by sorry
