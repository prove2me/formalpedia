-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_of_subset_eb0277a5cb67
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_of_subset_eb0277a5cb67
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:26.096667+00:00
-- url     : https://prove2.me/theorems/7300f84a-0029-4f3f-a29d-f7b363fc8b47
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Point Generated mem sub iff of subset eb0277a5cb67: P2 M Ground Theory Heights  Heights Kleiman Point Generated mem sub iff of subset eb0277a5cb67
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Point Generated mem sub iff of subset eb0277a5cb67 construction uses the P2 M Ground Theory Heights  Heights Kleiman Point Generated mem sub iff of subset eb0277a5cb67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPointGenerated.lean#L46-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPointGenerated.lean#L46-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPointGenerated
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
open GroundTheory.Heights₂.Heights.Kleiman.PointGenerated
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_of_subset_eb0277a5cb67 (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) {I J : Chart x}
    (h : I.1 ⊆ J.1) (y : Ω) : y ∈ Q.sub J ↔ y ∈ Q.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«PointGenerated».«mem_sub_iff_of_subset» := P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_of_subset_eb0277a5cb67
