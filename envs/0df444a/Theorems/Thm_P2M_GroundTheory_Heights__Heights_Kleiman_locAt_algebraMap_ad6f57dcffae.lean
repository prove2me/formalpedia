-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_algebraMap_ad6f57dcffae
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locAt_algebraMap_ad6f57dcffae
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:33:54.930427+00:00
-- url     : https://prove2.me/theorems/f80fe6fe-a893-5fbb-bf3f-9899a37fb1e4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc At algebra Map ad6f57dcffae: P2 M Ground Theory Heights  Heights Kleiman loc At algebra Map ad6f57dcffae
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc At algebra Map ad6f57dcffae construction uses the P2 M Ground Theory Heights  Heights Kleiman loc At algebra Map ad6f57dcffae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L63-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L63-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')
variable {k x y}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locAt_algebraMap_ad6f57dcffae (c : k) :
    algebraMap k Ω c ∈ locAt k x y ∧ redAt k x y (algebraMap k Ω c) = algebraMap k K' c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locAt_algebraMap» := P2M_GroundTheory_Heights__Heights_Kleiman_locAt_algebraMap_ad6f57dcffae
