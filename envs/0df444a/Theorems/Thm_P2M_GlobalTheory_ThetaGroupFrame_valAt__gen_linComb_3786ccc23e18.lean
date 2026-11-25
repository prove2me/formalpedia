-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_linComb_3786ccc23e18
-- name    : P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_linComb_3786ccc23e18
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:13.15067+00:00
-- url     : https://prove2.me/theorems/deaa7339-43d3-44f7-acc3-272db746ce98
-- title:
--   P2 M Global Theory Theta Group Frame val At  gen lin Comb 3786ccc23e18: P2 M Global Theory Theta Group Frame val At  gen lin Comb 3786ccc23e18
-- statement:
--   The P2 M Global Theory Theta Group Frame val At  gen lin Comb 3786ccc23e18 construction uses the P2 M Global Theory Theta Group Frame val At  gen lin Comb 3786ccc23e18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L65-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L65-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame

theorem P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_linComb_3786ccc23e18 (hv : ValLaws) {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen)
    (x : Sp ℂ ⟶ Y) (j j' : K → L.ι) (hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j)
    (hj' : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j') :
    valAt' x (LB.wchart L φ j) (c.s j).val =
      (∏ k, valAt' (x ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valAt' x (LB.wchart L φ j') (c.s j').val := by sorry

alias «GlobalTheory».«ThetaGroupFrame».«valAt'_gen_linComb» := P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_linComb_3786ccc23e18
