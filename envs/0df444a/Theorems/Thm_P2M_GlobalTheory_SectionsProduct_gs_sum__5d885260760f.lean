-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SectionsProduct_gs_sum__5d885260760f
-- name    : P2M_GlobalTheory_SectionsProduct_gs_sum__5d885260760f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:40.690469+00:00
-- url     : https://prove2.me/theorems/b995c365-f873-48a3-81a3-6c71db9f7ebd
-- title:
--   P2 M Global Theory Sections Product gs sum  5d885260760f: P2 M Global Theory Sections Product gs sum  5d885260760f
-- statement:
--   The P2 M Global Theory Sections Product gs sum  5d885260760f construction uses the P2 M Global Theory Sections Product gs sum  5d885260760f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionLinCombFiberProductSeparated.lean#L131-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionLinCombFiberProductSeparated.lean#L131-L132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.SectionsProduct
open GlobalTheory.KuennethOne
variable {B Y T S X₁ X₂ W : Scheme.{0}} {L : LB B} {K : Type} [Fintype K]

theorem P2M_GlobalTheory_SectionsProduct_gs_sum__5d885260760f (r : T ⟶ Y) (z : T) (U : Y.Opens) (h : r z ∈ U) {n : ℕ} (a : Fin n → Γ(Y, U)) :
    gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by sorry

alias «GlobalTheory».«SectionsProduct».«gs_sum'» := P2M_GlobalTheory_SectionsProduct_gs_sum__5d885260760f
