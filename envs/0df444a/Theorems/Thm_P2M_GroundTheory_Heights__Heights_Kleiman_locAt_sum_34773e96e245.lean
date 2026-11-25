-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_sum_34773e96e245
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locAt_sum_34773e96e245
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:43.278053+00:00
-- url     : https://prove2.me/theorems/8b77484a-cc5f-5643-b463-7064e46ae609
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc At sum 34773e96e245: P2 M Ground Theory Heights  Heights Kleiman loc At sum 34773e96e245
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc At sum 34773e96e245 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc At sum 34773e96e245 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L119-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L119-L128

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locAt_sum_34773e96e245 {ι : Type*} (s : Finset ι) (a : ι → Ω) (ha : ∀ i ∈ s, a i ∈ locAt k x y) :
    ∑ i ∈ s, a i ∈ locAt k x y ∧ redAt k x y (∑ i ∈ s, a i) = ∑ i ∈ s, redAt k x y (a i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locAt_sum» := P2M_GroundTheory_Heights__Heights_Kleiman_locAt_sum_34773e96e245
