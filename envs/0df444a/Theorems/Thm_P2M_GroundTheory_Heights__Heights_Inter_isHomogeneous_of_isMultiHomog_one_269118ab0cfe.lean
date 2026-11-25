-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isHomogeneous_of_isMultiHomog_one_269118ab0cfe
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isHomogeneous_of_isMultiHomog_one_269118ab0cfe
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:52.006408+00:00
-- url     : https://prove2.me/theorems/23d3a5e4-f245-472b-b84b-bd5b38fb2721
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Homogeneous of is Multi Homog one 269118ab0cfe: P2 M Ground Theory Heights  Heights Inter is Homogeneous of is Multi Homog one 269118ab0cfe
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Homogeneous of is Multi Homog one 269118ab0cfe construction uses the P2 M Ground Theory Heights  Heights Inter is Homogeneous of is Multi Homog one 269118ab0cfe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHomogeneousOfIsMultiHomogOne.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHomogeneousOfIsMultiHomogOne.lean#L35-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLineFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLinearQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHomogeneousOfIsMultiHomogOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
variable {F : Type} [Field F]

theorem P2M_GroundTheory_Heights__Heights_Inter_isHomogeneous_of_isMultiHomog_one_269118ab0cfe {K₀ : Type} [Fintype K₀] {ι₀ : K₀ → Type}
    [∀ k, Fintype (ι₀ k)] (hK : Fintype.card K₀ = 1) {f : MRingOver F ι₀}
    (hf : IsMultiHomog f fun _ => 1) : f.IsHomogeneous 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isHomogeneous_of_isMultiHomog_one» := P2M_GroundTheory_Heights__Heights_Inter_isHomogeneous_of_isMultiHomog_one_269118ab0cfe
