-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UU_ExpLinC_gs_sum__4b10aeea308e
-- name    : P2M_GlobalTheory_UU_ExpLinC_gs_sum__4b10aeea308e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:12:17.910224+00:00
-- url     : https://prove2.me/theorems/df8662d7-751d-4f32-b691-5e01aa9d760c
-- title:
--   P2 M Global Theory UU Exp Lin C gs sum  4b10aeea308e: P2 M Global Theory UU Exp Lin C gs sum  4b10aeea308e
-- statement:
--   The P2 M Global Theory UU Exp Lin C gs sum  4b10aeea308e construction uses the P2 M Global Theory UU Exp Lin C gs sum  4b10aeea308e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalLincomb.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalLincomb.lean#L18-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalLincomb
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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ExpLinC

theorem P2M_GlobalTheory_UU_ExpLinC_gs_sum__4b10aeea308e {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hm : r z ∈ U) {K : Type} (S : Finset K)
    (a : K → Γ(Y, U)) : gs r z U (∑ i ∈ S, a i) = ∑ i ∈ S, gs r z U (a i) := by sorry

alias «GlobalTheory».«UU».«ExpLinC».«gs_sum'» := P2M_GlobalTheory_UU_ExpLinC_gs_sum__4b10aeea308e
