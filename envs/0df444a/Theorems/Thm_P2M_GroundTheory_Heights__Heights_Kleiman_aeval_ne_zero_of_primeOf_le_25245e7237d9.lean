-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_aeval_ne_zero_of_primeOf_le_25245e7237d9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_aeval_ne_zero_of_primeOf_le_25245e7237d9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:33:41.09458+00:00
-- url     : https://prove2.me/theorems/eac59cbc-a19d-4bf2-a6ea-d078af0003c0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman aeval ne zero of prime Of le 25245e7237d9: P2 M Ground Theory Heights  Heights Kleiman aeval ne zero of prime Of le 25245e7237d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman aeval ne zero of prime Of le 25245e7237d9 construction uses the P2 M Ground Theory Heights  Heights Kleiman aeval ne zero of prime Of le 25245e7237d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L31-L33

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_aeval_ne_zero_of_primeOf_le_25245e7237d9 (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
    {s : Poly k N} {e : ℕ} (hs : s.IsHomogeneous e) (h : aeval y s ≠ 0) : aeval x s ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«aeval_ne_zero_of_primeOf_le» := P2M_GroundTheory_Heights__Heights_Kleiman_aeval_ne_zero_of_primeOf_le_25245e7237d9
