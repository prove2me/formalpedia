-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_swapCoord_standard_1189ac811217
-- name    : P2M_GroundTheory_Heights__Heights_swapCoord_standard_1189ac811217
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:33.733633+00:00
-- url     : https://prove2.me/theorems/6f63b11e-66e7-5c11-9744-edf8c0d3b359
-- title:
--   P2 M Ground Theory Heights  Heights swap Coord standard 1189ac811217: P2 M Ground Theory Heights  Heights swap Coord standard 1189ac811217
-- statement:
--   The P2 M Ground Theory Heights  Heights swap Coord standard 1189ac811217 construction uses the P2 M Ground Theory Heights  Heights swap Coord standard 1189ac811217 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L194-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L194-L209

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_swapCoord_standard_1189ac811217 :
    (FullLattice.standard K 2).carrier.map ((swapCoord (K := K)).toLinearMap.restrictScalars (𝓞 K)) =
      (FullLattice.standard K 2).carrier := by sorry

alias «GroundTheory».«Heights₂».«Heights».«swapCoord_standard» := P2M_GroundTheory_Heights__Heights_swapCoord_standard_1189ac811217
