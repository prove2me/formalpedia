-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_mem_ampleRing_twist_d5a9cb6bd913
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_mem_ampleRing_twist_d5a9cb6bd913
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:41.046921+00:00
-- url     : https://prove2.me/theorems/d5d785cb-9810-4832-9a92-45669c61eef0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem of mem ample Ring twist d5a9cb6bd913: P2 M Ground Theory Heights  Heights Kleiman mem of mem ample Ring twist d5a9cb6bd913
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem of mem ample Ring twist d5a9cb6bd913 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem of mem ample Ring twist d5a9cb6bd913 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L204-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L204-L227

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {L G : SubSystem k x Ω} {r₁ s₁ : ℕ} {h : Fin (r₁ + 1) → Ω} {g : Fin (s₁ + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_mem_ampleRing_twist_d5a9cb6bd913 (hL : IsVeryAmpleBy L h)
    (hgg : ∀ I, Submodule.span (chartRing k x I) (Set.range g) = G.sub I) {l : Fin (r₁ + 1)}
    {j : Fin (s₁ + 1)} (hl : h l ≠ 0) (hj : g j ≠ 0) {B : Subalgebra k Ω}
    (hB : ∀ a b, h a * g b / (h l * g j) ∈ B) {z : Ω}
    (hz : z ∈ ampleRing (L.twist G) 1 (h l * g j)) : z ∈ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_of_mem_ampleRing_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_mem_ampleRing_twist_d5a9cb6bd913
