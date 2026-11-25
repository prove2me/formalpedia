-- Prove2me | Theorems.Thm_P2M_GlobalTheory_NodalCubic_comp_toSpec__bbfc5e339852
-- name    : P2M_GlobalTheory_NodalCubic_comp_toSpec__bbfc5e339852
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:06:37.026688+00:00
-- url     : https://prove2.me/theorems/ba88f98f-4b69-5e23-a031-e78ad16afa34
-- title:
--   P2 M Global Theory Nodal Cubic comp to Spec  bbfc5e339852: P2 M Global Theory Nodal Cubic comp to Spec  bbfc5e339852
-- statement:
--   The P2 M Global Theory Nodal Cubic comp to Spec  bbfc5e339852 construction uses the P2 M Global Theory Nodal Cubic comp to Spec  bbfc5e339852 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RangeSubsetOfForallField.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RangeSubsetOfForallField.lean#L25-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonsingularIffNodal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField
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
open GlobalTheory GlobalTheory.NodalCubic
open GlobalTheory.WeierstrassCurve

theorem P2M_GlobalTheory_NodalCubic_comp_toSpec__bbfc5e339852 {Z : Scheme.{0}} {k : Type} [CommRing k] (x : Spec (.of k) ⟶ Z) :
    x ≫ Z.toSpecΓ = Spec.map (CommRingCat.ofHom (evalAt x)) := by sorry

alias «GlobalTheory».«NodalCubic».«comp_toSpecΓ» := P2M_GlobalTheory_NodalCubic_comp_toSpec__bbfc5e339852
