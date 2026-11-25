-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GeneratorFunctor_pb___injective_9545ad52f383
-- name    : P2M_GlobalTheory_GeneratorFunctor_pb___injective_9545ad52f383
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:07:18.03315+00:00
-- url     : https://prove2.me/theorems/4157c6a9-1515-478b-b33f-9b1b2c70ef02
-- title:
--   P2 M Global Theory Generator Functor pb   injective 9545ad52f383: P2 M Global Theory Generator Functor pb   injective 9545ad52f383
-- statement:
--   The P2 M Global Theory Generator Functor pb   injective 9545ad52f383 construction uses the P2 M Global Theory Generator Functor pb   injective 9545ad52f383 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L155-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L155-L165

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
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
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false

theorem P2M_GlobalTheory_GeneratorFunctor_pb___injective_9545ad52f383 {Y : Scheme.{0}} (W : Y.Opens) (h : ⊤ ≤ W.ι ⁻¹ᵁ W) :
    Function.Injective (pb W.ι W ⊤ h) := by sorry

alias «GlobalTheory».«GeneratorFunctor».«pb_ι_injective» := P2M_GlobalTheory_GeneratorFunctor_pb___injective_9545ad52f383
