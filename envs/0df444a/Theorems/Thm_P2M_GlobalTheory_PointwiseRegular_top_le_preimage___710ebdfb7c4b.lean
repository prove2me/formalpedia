-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PointwiseRegular_top_le_preimage___710ebdfb7c4b
-- name    : P2M_GlobalTheory_PointwiseRegular_top_le_preimage___710ebdfb7c4b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:49.594838+00:00
-- url     : https://prove2.me/theorems/0ff96bff-864c-4089-b217-5dd200d0bdc2
-- title:
--   P2 M Global Theory Pointwise Regular top le preimage   710ebdfb7c4b: P2 M Global Theory Pointwise Regular top le preimage   710ebdfb7c4b
-- statement:
--   The P2 M Global Theory Pointwise Regular top le preimage   710ebdfb7c4b construction uses the P2 M Global Theory Pointwise Regular top le preimage   710ebdfb7c4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsUniqueHomOfLocallyRegular.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsUniqueHomOfLocallyRegular.lean#L39-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniqueHomOfLocallyRegular
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
open GlobalTheory
open GlobalTheory.PointwiseRegular

theorem P2M_GlobalTheory_PointwiseRegular_top_le_preimage___710ebdfb7c4b {Y : Scheme.{0}} (U : Y.Opens) (y : Sp ℂ ⟶ U.toScheme) : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := by sorry

alias «GlobalTheory».«PointwiseRegular».«top_le_preimage_ι» := P2M_GlobalTheory_PointwiseRegular_top_le_preimage___710ebdfb7c4b
