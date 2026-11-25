-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_iterLim_eq_of_monotone_e11b6f1f0d13
-- name    : P2M_GroundTheory_Heights__Heights_iterLim_eq_of_monotone_e11b6f1f0d13
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:13.571128+00:00
-- url     : https://prove2.me/theorems/fe48528d-b159-515f-b99d-afbd15200d9a
-- title:
--   P2 M Ground Theory Heights  Heights iter Lim eq of monotone e11b6f1f0d13: P2 M Ground Theory Heights  Heights iter Lim eq of monotone e11b6f1f0d13
-- statement:
--   The P2 M Ground Theory Heights  Heights iter Lim eq of monotone e11b6f1f0d13 construction uses the P2 M Ground Theory Heights  Heights iter Lim eq of monotone e11b6f1f0d13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/MonotoneDoubleLimit.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/MonotoneDoubleLimit.lean#L8-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonotoneDoubleLimit
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
open Filter Topology

theorem P2M_GroundTheory_Heights__Heights_iterLim_eq_of_monotone_e11b6f1f0d13 {T : ℝ → ℝ → ℝ} {A B : ℝ → ℝ} {a b : ℝ}
    (hε : ∀ δ, 0 < δ → ∀ ε, 0 < ε → ∀ ε', ε ≤ ε' → T ε δ ≤ T ε' δ)
    (hδ : ∀ ε, 0 < ε → ∀ δ, 0 < δ → ∀ δ', δ ≤ δ' → T ε δ ≤ T ε δ')
    (hA : ∀ δ, 0 < δ → Tendsto (fun ε => T ε δ) (𝓝[>] 0) (𝓝 (A δ)))
    (hB : ∀ ε, 0 < ε → Tendsto (fun δ => T ε δ) (𝓝[>] 0) (𝓝 (B ε)))
    (ha : Tendsto A (𝓝[>] 0) (𝓝 a)) (hb : Tendsto B (𝓝[>] 0) (𝓝 b)) : a = b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«iterLim_eq_of_monotone» := P2M_GroundTheory_Heights__Heights_iterLim_eq_of_monotone_e11b6f1f0d13
