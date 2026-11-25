-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_diffStep_comm_16b0beed7080
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_diffStep_comm_16b0beed7080
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:04:33.348338+00:00
-- url     : https://prove2.me/theorems/c8a7d784-e328-463f-9a74-6dd19ab719fd
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel diff Step comm 16b0beed7080: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel diff Step comm 16b0beed7080
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel diff Step comm 16b0beed7080 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel diff Step comm 16b0beed7080 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L112-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_diffStep_comm_16b0beed7080 (a b : K → ℤ) (h : (K → ℤ) → ℤ) :
    diffStep a (diffStep b h) = diffStep b (diffStep a h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«diffStep_comm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_diffStep_comm_16b0beed7080
