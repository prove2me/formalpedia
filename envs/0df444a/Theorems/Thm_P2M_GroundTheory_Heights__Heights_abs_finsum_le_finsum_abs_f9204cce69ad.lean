-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_abs_finsum_le_finsum_abs_f9204cce69ad
-- name    : P2M_GroundTheory_Heights__Heights_abs_finsum_le_finsum_abs_f9204cce69ad
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:50.452098+00:00
-- url     : https://prove2.me/theorems/391bb471-c952-53e1-b683-5134619591c2
-- title:
--   P2 M Ground Theory Heights  Heights abs finsum le finsum abs f9204cce69ad: P2 M Ground Theory Heights  Heights abs finsum le finsum abs f9204cce69ad
-- statement:
--   The P2 M Ground Theory Heights  Heights abs finsum le finsum abs f9204cce69ad construction uses the P2 M Ground Theory Heights  Heights abs finsum le finsum abs f9204cce69ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOff.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOff.lean#L14-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_abs_finsum_le_finsum_abs_f9204cce69ad {α : Type*} (f : α → ℝ) : |∑ᶠ i, f i| ≤ ∑ᶠ i, |f i| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«abs_finsum_le_finsum_abs» := P2M_GroundTheory_Heights__Heights_abs_finsum_le_finsum_abs_f9204cce69ad
