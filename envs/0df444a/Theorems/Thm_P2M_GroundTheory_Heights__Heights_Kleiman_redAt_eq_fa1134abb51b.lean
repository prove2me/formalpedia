-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redAt_eq_fa1134abb51b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redAt_eq_fa1134abb51b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:31:09.233832+00:00
-- url     : https://prove2.me/theorems/b7c55d94-9161-5b86-9569-61501cd9b2ec
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red At eq fa1134abb51b: P2 M Ground Theory Heights  Heights Kleiman red At eq fa1134abb51b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red At eq fa1134abb51b construction uses the P2 M Ground Theory Heights  Heights Kleiman red At eq fa1134abb51b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L42-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L42-L61

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redAt_eq_fa1134abb51b {f s : Poly k N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s.IsHomogeneous e)
    (h : aeval y s ≠ 0) : redAt k x y (aeval x f / aeval x s) = aeval y f / aeval y s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redAt_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_redAt_eq_fa1134abb51b
