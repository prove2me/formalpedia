-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_fb592b680e04
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_fb592b680e04
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:02:39.137927+00:00
-- url     : https://prove2.me/theorems/a57c456c-7a38-5fad-8676-5612e8d3109a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Ring twist fb592b680e04: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Ring twist fb592b680e04
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Ring twist fb592b680e04 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Ring twist fb592b680e04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L96-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosed
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
open scoped Pointwise
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_fb592b680e04 (G H : SubSystem S x Ω) {h g : Ω} (hg : g ∈ G.secs) {u : Ω}
    (hu : u ∈ ampleRing H 1 h) : u ∈ ampleRing (G.twist H) 1 (h * g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«ampleRing_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_fb592b680e04
