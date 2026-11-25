-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_truncCoord_of_le_bb68e2da1b41
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_truncCoord_of_le_bb68e2da1b41
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:55.387171+00:00
-- url     : https://prove2.me/theorems/b1b76dbd-81f6-46a2-bd4a-e6a59a06a361
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof trunc Coord of le bb68e2da1b41: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof trunc Coord of le bb68e2da1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof trunc Coord of le bb68e2da1b41 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof trunc Coord of le bb68e2da1b41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L157-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L157-L160

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_truncCoord_of_le_bb68e2da1b41 {N : ℕ} {Φ : Type*} [Zero Φ] (t : Fin N → Φ) {i : ℕ} (h : N ≤ i) :
    truncCoord t i = t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«truncCoord_of_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_truncCoord_of_le_bb68e2da1b41
