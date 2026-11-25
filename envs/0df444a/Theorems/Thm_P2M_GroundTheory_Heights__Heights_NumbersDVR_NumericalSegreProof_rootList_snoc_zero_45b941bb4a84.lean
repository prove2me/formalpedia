-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_snoc_zero_45b941bb4a84
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_snoc_zero_45b941bb4a84
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:57.727031+00:00
-- url     : https://prove2.me/theorems/d1bd9542-e908-4ded-803f-819c0e50bb38
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List snoc zero 45b941bb4a84: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List snoc zero 45b941
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List snoc zero 45b941bb4a84 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List snoc zero 45b941bb4a84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L93-L96

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_snoc_zero_45b941bb4a84 {i : ℕ} (x : Fin (i + 1) → K → ℤ) (α : Fin i → ℕ) :
    rootList x (Fin.snoc α 0) = rootList (fun j => x (Fin.castSucc j)) α := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«rootList_snoc_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_snoc_zero_45b941bb4a84
