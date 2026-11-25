-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TorusDefect_exists_eq_univ__ffa80484f647
-- name    : P2M_GlobalTheory_TorusDefect_exists_eq_univ__ffa80484f647
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:44:08.279015+00:00
-- url     : https://prove2.me/theorems/784468ce-90a3-4bf0-8c52-816e996ccf35
-- title:
--   P2 M Global Theory Torus Defect exists eq univ  ffa80484f647: P2 M Global Theory Torus Defect exists eq univ  ffa80484f647
-- statement:
--   The P2 M Global Theory Torus Defect exists eq univ  ffa80484f647 construction uses the P2 M Global Theory Torus Defect exists eq univ  ffa80484f647 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIsMonHomSplitTorusOfSqEqBot.lean#L65-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIsMonHomSplitTorusOfSqEqBot.lean#L65-L75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isMonHom_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (epsR IsLieBasis isMonHom_of_mul)
open scoped CategoryTheory.Obj
open AddMonoidAlgebra (single mapDomainAlgHom)
open GlobalTheory GlobalTheory.TorusDefect
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SqZero GlobalTheory.Diag
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
  {C C' : Type} [CommRing C] [Algebra A C] [CommRing C'] [Algebra A C']

theorem P2M_GlobalTheory_TorusDefect_exists_eq_univ__ffa80484f647 (v w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) :
    ∃ φ : AddMonoidAlgebra A (X × X) →ₐ[A] C,
      spMap (φ.comp (mapDomainAlgHom A A (AddMonoidHom.inl X X))) ≫ univ A X = v ∧
      spMap (φ.comp (mapDomainAlgHom A A (AddMonoidHom.inr X X))) ≫ univ A X = w := by sorry

alias «GlobalTheory».«TorusDefect».«exists_eq_univ₂» := P2M_GlobalTheory_TorusDefect_exists_eq_univ__ffa80484f647
