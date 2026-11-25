-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domSub_iff_f130a9a451ae
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domSub_iff_f130a9a451ae
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:22:12.748792+00:00
-- url     : https://prove2.me/theorems/b922f119-fe08-5c17-a4a0-1020d10c5004
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination mem dom Sub iff f130a9a451ae: P2 M Ground Theory Heights  Heights Kleiman Domination mem dom Sub iff f130a9a451ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination mem dom Sub iff f130a9a451ae construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination mem dom Sub iff f130a9a451ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L247-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L247-L248

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
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
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domSub_iff_f130a9a451ae (b : Ω) : b ∈ domSub (S := S) x' hi ↔ b ∈ domRing S x x' i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«mem_domSub_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domSub_iff_f130a9a451ae
