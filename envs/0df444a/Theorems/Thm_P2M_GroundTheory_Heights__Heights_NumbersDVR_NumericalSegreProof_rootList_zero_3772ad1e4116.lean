-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_zero_3772ad1e4116
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_zero_3772ad1e4116
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:16.257797+00:00
-- url     : https://prove2.me/theorems/791fcff3-b030-4751-a42a-fc275b1f9984
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List zero 3772ad1e4116: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List zero 3772ad1e4116
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List zero 3772ad1e4116 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List zero 3772ad1e4116 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L109-L110

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_zero_3772ad1e4116 {n : ℕ} (x : Fin n → K → ℤ) : rootList x 0 = [] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«rootList_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_zero_3772ad1e4116
