-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_nonneg_c1cc390decae
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_nonneg_c1cc390decae
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:44.711981+00:00
-- url     : https://prove2.me/theorems/9f3651bd-872b-4fb8-94a6-5cbdd57ade80
-- title:
--   P2 M Ground Theory Heights  Heights KAlt frob Delta nonneg c1cc390decae: P2 M Ground Theory Heights  Heights KAlt frob Delta nonneg c1cc390decae
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt frob Delta nonneg c1cc390decae construction uses the P2 M Ground Theory Heights  Heights KAlt frob Delta nonneg c1cc390decae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L75-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
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
open Finset
open GroundTheory.Heights₂.Heights.KAlt

theorem P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_nonneg_c1cc390decae {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) : 0 ≤ frobDelta ν := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«frobDelta_nonneg» := P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_nonneg_c1cc390decae
