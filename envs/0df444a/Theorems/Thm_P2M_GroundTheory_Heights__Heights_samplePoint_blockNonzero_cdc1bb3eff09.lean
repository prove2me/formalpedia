-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_samplePoint_blockNonzero_cdc1bb3eff09
-- name    : P2M_GroundTheory_Heights__Heights_samplePoint_blockNonzero_cdc1bb3eff09
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:47:54.407438+00:00
-- url     : https://prove2.me/theorems/7f07fc38-463b-4d7a-9bcf-adea5056443e
-- title:
--   P2 M Ground Theory Heights  Heights sample Point block Nonzero cdc1bb3eff09: P2 M Ground Theory Heights  Heights sample Point block Nonzero cdc1bb3eff09
-- statement:
--   The P2 M Ground Theory Heights  Heights sample Point block Nonzero cdc1bb3eff09 construction uses the P2 M Ground Theory Heights  Heights sample Point block Nonzero cdc1bb3eff09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L231-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L231-L234

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_samplePoint_blockNonzero_cdc1bb3eff09 : BlockNonzero samplePoint := by sorry

alias «GroundTheory».«Heights₂».«Heights».«samplePoint_blockNonzero» := P2M_GroundTheory_Heights__Heights_samplePoint_blockNonzero_cdc1bb3eff09
