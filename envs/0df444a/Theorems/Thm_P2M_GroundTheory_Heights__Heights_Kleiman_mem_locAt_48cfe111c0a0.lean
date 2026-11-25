-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_locAt_48cfe111c0a0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_locAt_48cfe111c0a0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:32:30.496706+00:00
-- url     : https://prove2.me/theorems/cd3dbf2e-e676-46d1-a496-abc76db0931e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem loc At 48cfe111c0a0: P2 M Ground Theory Heights  Heights Kleiman mem loc At 48cfe111c0a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem loc At 48cfe111c0a0 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem loc At 48cfe111c0a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L35-L37

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_locAt_48cfe111c0a0 {f s : Poly k N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s.IsHomogeneous e)
    (h : aeval y s ≠ 0) : aeval x f / aeval x s ∈ locAt k x y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_locAt» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_locAt_48cfe111c0a0
