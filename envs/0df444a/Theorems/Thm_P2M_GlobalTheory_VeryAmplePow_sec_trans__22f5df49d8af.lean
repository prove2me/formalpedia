-- Prove2me | Theorems.Thm_P2M_GlobalTheory_VeryAmplePow_sec_trans__22f5df49d8af
-- name    : P2M_GlobalTheory_VeryAmplePow_sec_trans__22f5df49d8af
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:55.21775+00:00
-- url     : https://prove2.me/theorems/c3f248e5-8390-45fb-82b4-f3f50d25d99b
-- title:
--   P2 M Global Theory Very Ample Pow sec trans  22f5df49d8af: P2 M Global Theory Very Ample Pow sec trans  22f5df49d8af
-- statement:
--   The P2 M Global Theory Very Ample Pow sec trans  22f5df49d8af construction uses the P2 M Global Theory Very Ample Pow sec trans  22f5df49d8af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L139-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L139-L144

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem P2M_GlobalTheory_VeryAmplePow_sec_trans__22f5df49d8af {Z Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) (r : Z ⟶ Y) (z : Z) {j j' : M.ι}
    (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') :
    gs r z (M.U j) (s.f j) = (gm r z _ (M.g j j')).val * gs r z (M.U j') (s.f j') := by sorry

alias «GlobalTheory».«VeryAmplePow».«sec_trans'» := P2M_GlobalTheory_VeryAmplePow_sec_trans__22f5df49d8af
