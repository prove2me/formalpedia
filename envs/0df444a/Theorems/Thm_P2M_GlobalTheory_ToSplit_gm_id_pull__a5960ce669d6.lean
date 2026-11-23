-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ToSplit_gm_id_pull__a5960ce669d6
-- name    : P2M_GlobalTheory_ToSplit_gm_id_pull__a5960ce669d6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:02.541145+00:00
-- url     : https://prove2.me/theorems/49d49c1d-8920-43e5-8d2b-8b37c6312793
-- title:
--   P2 M Global Theory To Split gm id pull  a5960ce669d6: P2 M Global Theory To Split gm id pull  a5960ce669d6
-- statement:
--   The P2 M Global Theory To Split gm id pull  a5960ce669d6 construction uses the P2 M Global Theory To Split gm id pull  a5960ce669d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtDatumOfSplitTorusExtension.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtDatumOfSplitTorusExtension.lean#L46-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
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
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}

theorem P2M_GlobalTheory_ToSplit_gm_id_pull__a5960ce669d6 (f : Y ⟶ X) (y : Y) {U : X.Opens} (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm (𝟙 Y) y (f ⁻¹ᵁ U) (pullU f U a) = gm f y U a := by sorry

alias «GlobalTheory».«ToSplit».«gm_id_pull'» := P2M_GlobalTheory_ToSplit_gm_id_pull__a5960ce669d6
