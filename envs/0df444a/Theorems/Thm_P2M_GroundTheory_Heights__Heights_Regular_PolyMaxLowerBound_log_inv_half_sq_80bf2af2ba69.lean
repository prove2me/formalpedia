-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_log_inv_half_sq_80bf2af2ba69
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_log_inv_half_sq_80bf2af2ba69
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:17:47.839805+00:00
-- url     : https://prove2.me/theorems/38c55963-9b81-4ba7-89b3-7fa3bb92133e
-- title:
--   P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound log inv half sq 80bf2af2ba69: P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound log inv half sq 80bf2af2ba69
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound log inv half sq 80bf2af2ba69 construction uses the P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound log inv half sq 80bf2af2ba69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PPolyMaxLowerBound.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PPolyMaxLowerBound.lean#L61-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PPolyMaxLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Set
open ReciprocityTheory.AnForm.A (polyMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_log_inv_half_sq_80bf2af2ba69 {t : ℝ} (ht : 0 < t) :
    Real.log ((t / 2) ^ 2)⁻¹ = 2 * Real.log 2 + 2 * Real.log t⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PolyMaxLowerBound».«log_inv_half_sq» := P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_log_inv_half_sq_80bf2af2ba69
