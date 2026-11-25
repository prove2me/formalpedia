-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_inv_mem_chartRing_cebcaeb7ef5d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_inv_mem_chartRing_cebcaeb7ef5d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:51.074591+00:00
-- url     : https://prove2.me/theorems/bfb20827-b669-4cbd-9ae0-5e9a187ad958
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Point Generated inv mem chart Ring cebcaeb7ef5d: P2 M Ground Theory Heights  Heights Kleiman Point Generated inv mem chart Ring cebcaeb7ef5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Point Generated inv mem chart Ring cebcaeb7ef5d construction uses the P2 M Ground Theory Heights  Heights Kleiman Point Generated inv mem chart Ring cebcaeb7ef5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPointGenerated.lean#L18-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPointGenerated.lean#L18-L44

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_inv_mem_chartRing_cebcaeb7ef5d (hx : IsSubvar x (primeOf (S := k) x) 0) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing k x I) : a⁻¹ ∈ chartRing k x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«PointGenerated».«inv_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_inv_mem_chartRing_cebcaeb7ef5d
