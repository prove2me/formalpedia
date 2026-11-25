-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockLine_inducesMetric_7152417dd2c8
-- name    : P2M_GroundTheory_Heights__Heights_blockLine_inducesMetric_7152417dd2c8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:51.447179+00:00
-- url     : https://prove2.me/theorems/17178c2a-ed76-472d-b5f9-d06022344ecb
-- title:
--   P2 M Ground Theory Heights  Heights block Line induces Metric 7152417dd2c8: P2 M Ground Theory Heights  Heights block Line induces Metric 7152417dd2c8
-- statement:
--   The P2 M Ground Theory Heights  Heights block Line induces Metric 7152417dd2c8 construction uses the P2 M Ground Theory Heights  Heights block Line induces Metric 7152417dd2c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L383-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L383-L434

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)

theorem P2M_GroundTheory_Heights__Heights_blockLine_inducesMetric_7152417dd2c8 (k₀ : ι) :
    (blockAddData n k₀).InducesMetric (wholePoint n) (blockAddData n k₀).elt (blockLine n k₀).toGeo
      (blockLine (blockAddData n k₀).extSizes none).toGeo := by sorry

alias «GroundTheory».«Heights₂».«Heights».«blockLine_inducesMetric» := P2M_GroundTheory_Heights__Heights_blockLine_inducesMetric_7152417dd2c8
