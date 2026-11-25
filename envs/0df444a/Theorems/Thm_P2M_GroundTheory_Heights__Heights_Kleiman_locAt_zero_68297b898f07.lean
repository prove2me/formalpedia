-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_zero_68297b898f07
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locAt_zero_68297b898f07
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:32:34.866666+00:00
-- url     : https://prove2.me/theorems/9db400a8-42ba-4e18-9673-377723dd7d9d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc At zero 68297b898f07: P2 M Ground Theory Heights  Heights Kleiman loc At zero 68297b898f07
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc At zero 68297b898f07 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc At zero 68297b898f07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L73-L74

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locAt_zero_68297b898f07 : (0 : Ω) ∈ locAt k x y ∧ redAt k x y (0 : Ω) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locAt_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_locAt_zero_68297b898f07
