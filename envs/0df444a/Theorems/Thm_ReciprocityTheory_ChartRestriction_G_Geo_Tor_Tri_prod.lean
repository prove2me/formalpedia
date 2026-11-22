-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Tri.prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:21.243324+00:00
-- url     : https://prove2.me/theorems/9f03dcc1-bc5c-48dd-8497-ffaf686bbf87
-- title:
--   Tri: prod
-- statement:
--   The Tri construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L359-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean#L359-L369

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
variable {K : Type} [Fintype K] {Y Y' Y'' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {φ'' : K → (Y'' ⟶ X'')}
  {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L' φ' ε)} {t'' : LB.Gen (LB.LinComb L'' φ'' ε)}
  {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.Tri.prod (T : Tri w w' w'') (hc : ∀ k, φ'' k ≫ F' = h' ≫ φ' k) (Z : Scheme.{0}) (r : Z ⟶ Y'') (z : Z)
    (p : K → L.ι) (i : K → L'.ι) (q : K → L''.ι) (hp : ∀ k, F (F' (φ'' k (r z))) ∈ L.U (p k))
    (hi : ∀ k, F' (φ'' k (r z)) ∈ L'.U (i k)) (hq : ∀ k, φ'' k (r z) ∈ L''.U (q k)) :
    ∏ k, gw w'' (r ≫ φ'' k) z (p k) (q k) ^ ε k =
      (∏ k, gw w ((r ≫ h') ≫ φ' k) z (p k) (i k) ^ ε k) * ∏ k, gw w' (r ≫ φ'' k) z (i k) (q k) ^ ε k := by sorry
