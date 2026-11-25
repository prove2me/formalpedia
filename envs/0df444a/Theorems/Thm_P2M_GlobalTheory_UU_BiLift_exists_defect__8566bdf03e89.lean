-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UU_BiLift_exists_defect__8566bdf03e89
-- name    : P2M_GlobalTheory_UU_BiLift_exists_defect__8566bdf03e89
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:07:18.059991+00:00
-- url     : https://prove2.me/theorems/5dbbd4c9-d4d7-4e37-91c5-89435b85c607
-- title:
--   P2 M Global Theory UU Bi Lift exists defect  8566bdf03e89: P2 M Global Theory UU Bi Lift exists defect  8566bdf03e89
-- statement:
--   The P2 M Global Theory UU Bi Lift exists defect  8566bdf03e89 construction uses the P2 M Global Theory UU Bi Lift exists defect  8566bdf03e89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsPullLam.lean#L132-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsPullLam.lean#L132-L148

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPullLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiLift
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
variable {H Y : Over S} [GrpObj H] {i : H ⟶ G} [IsMonHom i] {x : Y ⟶ G}
omit [IsMonHom i] [GrpObj H]

theorem P2M_GlobalTheory_UU_BiLift_exists_defect__8566bdf03e89 (s : LB.Gen (LB.LinComb L.L (lam (fst H G ≫ i) (snd H G)) Oε)) (hs : s.IsGen) :
    ∃ f : Γ((H ⊗ G ⊗ G).left, ⊤)ˣ, ∀ (Z : Over S) (t : Z ⟶ H) (y : Z ⟶ G ⊗ G) (z : Z.left) (J), Good L.L z J →
      val s (lift t (y ≫ fst _ _ * y ≫ snd _ _)).left z J = gm (lift t y).left z ⊤ f *
        (cubV c z J (t ≫ i) (y ≫ fst _ _) (y ≫ snd _ _) * val s (lift t (y ≫ fst _ _)).left z J *
          val s (lift t (y ≫ snd _ _)).left z J) := by sorry

alias «GlobalTheory».«UU».«BiLift».«exists_defect₂» := P2M_GlobalTheory_UU_BiLift_exists_defect__8566bdf03e89
