-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ExpGTrans_fam_B_pull_88ae84d64707
-- name    : P2M_GlobalTheory_ExpGTrans_fam_B_pull_88ae84d64707
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:33.324891+00:00
-- url     : https://prove2.me/theorems/0459d344-de2d-4cb1-a06e-da44c271dc17
-- title:
--   P2 M Global Theory Exp GTrans fam B pull 88ae84d64707: P2 M Global Theory Exp GTrans fam B pull 88ae84d64707
-- statement:
--   The P2 M Global Theory Exp GTrans fam B pull 88ae84d64707 construction uses the P2 M Global Theory Exp GTrans fam B pull 88ae84d64707 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsGTransport.lean#L142-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsGTransport.lean#L142-L173

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsGTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.ExpGTrans
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {D : DegPre R} {D' : DegPre R'}

theorem P2M_GlobalTheory_ExpGTrans_fam_B_pull_88ae84d64707 (hD : IsPullDeg φ D D') (x : D'.X) (κ : Fin 4) :
    D'.famφB x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.famφB (hD.xe x) κ := by sorry

alias «GlobalTheory».«ExpGTrans».«famφB_pull» := P2M_GlobalTheory_ExpGTrans_fam_B_pull_88ae84d64707
