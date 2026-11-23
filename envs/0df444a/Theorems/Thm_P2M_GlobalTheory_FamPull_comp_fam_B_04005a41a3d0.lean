-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FamPull_comp_fam_B_04005a41a3d0
-- name    : P2M_GlobalTheory_FamPull_comp_fam_B_04005a41a3d0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:22.168638+00:00
-- url     : https://prove2.me/theorems/e5daa695-31d3-493b-9738-db59886e60bd
-- title:
--   P2 M Global Theory Fam Pull comp fam B 04005a41a3d0: P2 M Global Theory Fam Pull comp fam B 04005a41a3d0
-- statement:
--   The P2 M Global Theory Fam Pull comp fam B 04005a41a3d0 construction uses the P2 M Global Theory Fam Pull comp fam B 04005a41a3d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean#L43-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
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
open GlobalTheory
open GlobalTheory.FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem P2M_GlobalTheory_FamPull_comp_fam_B_04005a41a3d0 {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (α : D.X) (i : Fin 4) :
    x.left ≫ D.famφB α i = (![x, cP D T α * x, cP D T α, 1] i).left := by sorry

alias «GlobalTheory».«FamPull».«comp_famφB» := P2M_GlobalTheory_FamPull_comp_fam_B_04005a41a3d0
