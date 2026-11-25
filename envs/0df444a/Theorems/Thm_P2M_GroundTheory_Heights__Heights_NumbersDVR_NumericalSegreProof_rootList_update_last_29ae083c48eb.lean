-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_update_last_29ae083c48eb
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_update_last_29ae083c48eb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:06.575639+00:00
-- url     : https://prove2.me/theorems/a369c64e-d523-47f1-9efc-cd221fc41f8e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List update last 29ae083c48eb: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List update last 29
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List update last 29ae083c48eb construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List update last 29ae083c48eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L99-L106

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
variable {K : Type*} [DecidableEq K]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_update_last_29ae083c48eb {i : ℕ} (x : Fin (i + 1) → K → ℤ) (β : Fin (i + 1) → ℕ) :
    rootList x (Function.update β (Fin.last i) (β (Fin.last i) + 1)) =
      rootList x β ++ [x (Fin.last i)] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«rootList_update_last» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_update_last_29ae083c48eb
