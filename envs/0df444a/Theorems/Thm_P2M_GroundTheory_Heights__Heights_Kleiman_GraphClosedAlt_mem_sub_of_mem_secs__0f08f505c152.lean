-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_mem_sub_of_mem_secs__0f08f505c152
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_mem_sub_of_mem_secs__0f08f505c152
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:40:21.012329+00:00
-- url     : https://prove2.me/theorems/f6d90bed-3dc2-4c88-94d0-408d56a3ff48
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt mem sub of mem secs  0f08f505c152: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt mem sub of mem secs  0f08f505c152
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt mem sub of mem secs  0f08f505c152 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt mem sub of mem secs  0f08f505c152 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L19-L22

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_mem_sub_of_mem_secs__0f08f505c152 {F : SubSystem S x Ω} {z : Ω} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«mem_sub_of_mem_secs'» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_mem_sub_of_mem_secs__0f08f505c152
