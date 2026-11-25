-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_div_084462a2e36e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locAt_div_084462a2e36e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:32:47.258393+00:00
-- url     : https://prove2.me/theorems/b65b7d43-0106-447a-8e34-2899583f3e10
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc At div 084462a2e36e: P2 M Ground Theory Heights  Heights Kleiman loc At div 084462a2e36e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc At div 084462a2e36e construction uses the P2 M Ground Theory Heights  Heights Kleiman loc At div 084462a2e36e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L140-L145

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locAt_div_084462a2e36e {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) (hr : redAt k x y b ≠ 0) :
    a / b ∈ locAt k x y ∧ redAt k x y (a / b) = redAt k x y a / redAt k x y b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locAt_div» := P2M_GroundTheory_Heights__Heights_Kleiman_locAt_div_084462a2e36e
