-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I4_isBlockMap_blkV
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I4.isBlockMap_blkV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:52.9468+00:00
-- url     : https://prove2.me/theorems/6f3c72e5-2946-47cc-ab11-18cf82c09709
-- title:
--   I4: is Block Map blk V
-- statement:
--   The I4 construction uses the is Block Map blk V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MixedFieldContraction/GenericFibreKerTarget.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MixedFieldContraction/GenericFibreKerTarget.lean#L128-L136

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.AI.I4.isBlockMap_blkV (κ : Type*) (b : Fin 2) :
    IsBlockMap (ι := fun _ : Unit => κ) (ι' := fun _ : Fin 2 => κ) (blkOf b) (blkV κ b) := by sorry
