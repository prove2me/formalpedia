-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:31:19.13286+00:00
-- url     : https://prove2.me/theorems/3b4086e4-7dd4-5d74-a64a-6fb48c36fabe
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman chart Ring sub loc At a84ca9ba7312: P2 M Ground Theory Heights  Heights Kleiman chart Ring sub loc At a84ca9ba7312
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman chart Ring sub loc At a84ca9ba7312 construction uses the P2 M Ground Theory Heights  Heights Kleiman chart Ring sub loc At a84ca9ba7312 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L147-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L147-L152

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312 (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I : Chart y) {a : Ω}
    (ha : a ∈ chartRing k x (liftChart hxy I)) :
    a ∈ locAt k x y ∧ redAt k x y a ∈ chartRing k y I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«chartRing_sub_locAt» := P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
