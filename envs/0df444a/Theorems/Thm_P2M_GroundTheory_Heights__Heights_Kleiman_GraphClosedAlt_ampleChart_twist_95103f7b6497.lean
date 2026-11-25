-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_twist_95103f7b6497
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_twist_95103f7b6497
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:05:54.943909+00:00
-- url     : https://prove2.me/theorems/cf3f280c-d5b9-5464-b326-430ef425fff4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart twist 95103f7b6497: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart twist 95103f7b6497
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart twist 95103f7b6497 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt ample Chart twist 95103f7b6497 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L85-L94

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_twist_95103f7b6497 (G H : SubSystem S x Ω) {h g : Ω} (I : Chart x) (hg : g ∈ G.sub I) {u : Ω}
    (hu : u ∈ ampleChart H 1 h I) : u ∈ ampleChart (G.twist H) 1 (h * g) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«ampleChart_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_twist_95103f7b6497
