-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_le_of_local_antilipschitz_c1a501dd5ea8
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_le_of_local_antilipschitz_c1a501dd5ea8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:56.365646+00:00
-- url     : https://prove2.me/theorems/dca509ae-24bf-4688-bd06-5ed0781e5f4a
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H le of local antilipschitz c1a501dd5ea8: P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H le of local antilipschitz c1a501dd5ea8
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H le of local antilipschitz c1a501dd5ea8 construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H le of local antilipschitz c1a501dd5ea8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L171-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L171-L196

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_le_of_local_antilipschitz_c1a501dd5ea8 {n r : ℕ} (f : (Fin n → ℂ) → (Fin r → ℂ))
    (S : Set (Fin n → ℂ))
    (h : ∀ x₀ ∈ S, ∃ U ∈ 𝓝 x₀, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ S ∩ U, ∀ x' ∈ S ∩ U, ‖x - x'‖ ≤ K * ‖f x - f x'‖) :
    dimH S ≤ 2 * (r : ENNReal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«dimH_le_of_local_antilipschitz» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_le_of_local_antilipschitz_c1a501dd5ea8
