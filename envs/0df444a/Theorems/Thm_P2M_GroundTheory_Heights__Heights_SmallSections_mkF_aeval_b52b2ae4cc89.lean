-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_b52b2ae4cc89
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_b52b2ae4cc89
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:31.179632+00:00
-- url     : https://prove2.me/theorems/50eb1c08-66d7-5d60-9273-17157b2fb94c
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections mk F aeval b52b2ae4cc89: P2 M Ground Theory Heights  Heights Small Sections mk F aeval b52b2ae4cc89
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections mk F aeval b52b2ae4cc89 construction uses the P2 M Ground Theory Heights  Heights Small Sections mk F aeval b52b2ae4cc89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L49-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_b52b2ae4cc89 (P : ArithVariety n) {σ : Type*} (g : σ → MvPolynomial (Coord n) ℤ)
    (F : MvPolynomial σ ℤ) : P.mkF (aeval g F) = aeval (fun j ↦ P.mkF (g j)) F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«mkF_aeval» := P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_b52b2ae4cc89
