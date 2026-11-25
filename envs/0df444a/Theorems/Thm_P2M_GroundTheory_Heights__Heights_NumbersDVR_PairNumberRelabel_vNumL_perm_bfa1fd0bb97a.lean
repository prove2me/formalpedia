-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_vNumL_perm_bfa1fd0bb97a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_vNumL_perm_bfa1fd0bb97a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:10:11.291988+00:00
-- url     : https://prove2.me/theorems/96c83294-43ad-4cd6-b517-b06a325c9a35
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel v Num L perm bfa1fd0bb97a: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel v Num L perm bfa1fd0bb97a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel v Num L perm bfa1fd0bb97a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel v Num L perm bfa1fd0bb97a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L135-L138

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
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_vNumL_perm_bfa1fd0bb97a (W : Ideal (MRing ι O)) {l₁ l₂ : List (K → ℤ)} (p : l₁.Perm l₂) :
    vNumL W l₁ = vNumL W l₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«vNumL_perm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_vNumL_perm_bfa1fd0bb97a
