-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaAmple_valAt__linComb_g_c2c02d34e6d0
-- name    : P2M_GlobalTheory_ThetaAmple_valAt__linComb_g_c2c02d34e6d0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:51.988067+00:00
-- url     : https://prove2.me/theorems/979be23a-6aeb-4ee7-89fc-d4bb81f436de
-- title:
--   P2 M Global Theory Theta Ample val At  lin Comb g c2c02d34e6d0: P2 M Global Theory Theta Ample val At  lin Comb g c2c02d34e6d0
-- statement:
--   The P2 M Global Theory Theta Ample val At  lin Comb g c2c02d34e6d0 construction uses the P2 M Global Theory Theta Ample val At  lin Comb g c2c02d34e6d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L35-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAmple

theorem P2M_GlobalTheory_ThetaAmple_valAt__linComb_g_c2c02d34e6d0 {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) {N : ℕ} (j j' : Fin N → L.ι) (x : Sp ℂ ⟶ Y)
    (h : ⊤ ≤ x ⁻¹ᵁ ((LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).U j ⊓
      (LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).U j')) :
    valAt' x _ ((LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).g j j').val =
      ∏ k, valAt' (x ≫ φ) _ (L.g (j k) (j' k)).val := by sorry

alias «GlobalTheory».«ThetaAmple».«valAt'_linComb_g» := P2M_GlobalTheory_ThetaAmple_valAt__linComb_g_c2c02d34e6d0
