-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TangentPow_ptMap_id__b9bbf1f25ce6
-- name    : P2M_GlobalTheory_TangentPow_ptMap_id__b9bbf1f25ce6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:46.460278+00:00
-- url     : https://prove2.me/theorems/30f7d5b2-e3e3-4e49-83e9-672d5a02321f
-- title:
--   P2 M Global Theory Tangent Pow pt Map id  b9bbf1f25ce6: P2 M Global Theory Tangent Pow pt Map id  b9bbf1f25ce6
-- statement:
--   The P2 M Global Theory Tangent Pow pt Map id  b9bbf1f25ce6 construction uses the P2 M Global Theory Tangent Pow pt Map id  b9bbf1f25ce6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowEqScaleAndExistsUniqueTorsion.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowEqScaleAndExistsUniqueTorsion.lean#L25-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.TangentPow
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem P2M_GlobalTheory_TangentPow_ptMap_id__b9bbf1f25ce6 (A : Type) [CommRing A] [Algebra O A] : ptMap (AlgHom.id O A) = 𝟙 _ := by sorry

alias «GlobalTheory».«TangentPow».«ptMap_id'» := P2M_GlobalTheory_TangentPow_ptMap_id__b9bbf1f25ce6
