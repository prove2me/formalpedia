-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_twist_pow_sub_866f2c84b38e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_twist_pow_sub_866f2c84b38e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:06:00.484318+00:00
-- url     : https://prove2.me/theorems/177ec2ab-dbdd-5fa2-9864-af85c3dc9095
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt twist pow sub 866f2c84b38e: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt twist pow sub 866f2c84b38e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt twist pow sub 866f2c84b38e construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt twist pow sub 866f2c84b38e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosed.lean#L81-L83

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_twist_pow_sub_866f2c84b38e (G H : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    ((G.twist H).pow n).sub I = (H.sub I * G.sub I) ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«twist_pow_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_twist_pow_sub_866f2c84b38e
