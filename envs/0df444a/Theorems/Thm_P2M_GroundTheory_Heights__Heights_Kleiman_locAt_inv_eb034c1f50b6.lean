-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_inv_eb034c1f50b6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locAt_inv_eb034c1f50b6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:31:12.6889+00:00
-- url     : https://prove2.me/theorems/ac7ad7d7-ec36-51d2-a844-34c06c17f4a6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc At inv eb034c1f50b6: P2 M Ground Theory Heights  Heights Kleiman loc At inv eb034c1f50b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc At inv eb034c1f50b6 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc At inv eb034c1f50b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L130-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L130-L138

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locAt_inv_eb034c1f50b6 {a : Ω} (ha : a ∈ locAt k x y) (hr : redAt k x y a ≠ 0) :
    a ≠ 0 ∧ a⁻¹ ∈ locAt k x y ∧ redAt k x y a⁻¹ = (redAt k x y a)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locAt_inv» := P2M_GroundTheory_Heights__Heights_Kleiman_locAt_inv_eb034c1f50b6
