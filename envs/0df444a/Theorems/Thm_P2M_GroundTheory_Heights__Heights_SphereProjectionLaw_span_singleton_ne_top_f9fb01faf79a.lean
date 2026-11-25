-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_span_singleton_ne_top_f9fb01faf79a
-- name    : P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_span_singleton_ne_top_f9fb01faf79a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:15.405195+00:00
-- url     : https://prove2.me/theorems/6725ca43-6c61-4be9-9b76-b31915ff93e7
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Projection Law span singleton ne top f9fb01faf79a: P2 M Ground Theory Heights  Heights Sphere Projection Law span singleton ne top f9fb01faf79a
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Projection Law span singleton ne top f9fb01faf79a construction uses the P2 M Ground Theory Heights  Heights Sphere Projection Law span singleton ne top f9fb01faf79a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L91-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw
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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereProjectionLaw
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_span_singleton_ne_top_f9fb01faf79a {N : ℕ} (hN : 2 ≤ N) (p : Fin N → ℂ) :
    Submodule.span ℂ {p} ≠ ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereProjectionLaw».«span_singleton_ne_top» := P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_span_singleton_ne_top_f9fb01faf79a
