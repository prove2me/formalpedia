-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mul_mem_span_1d57a849979c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mul_mem_span_1d57a849979c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:05:13.622493+00:00
-- url     : https://prove2.me/theorems/283a2cbe-420e-5867-9f32-dacf4b97bfc1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio mul mem span 1d57a849979c: P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio mul mem span 1d57a849979c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio mul mem span 1d57a849979c construction uses the P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio mul mem span 1d57a849979c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutNonempty.lean#L30-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutNonempty.lean#L30-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutNonempty
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mul_mem_span_1d57a849979c {L : SubSystem k x Ω} {s : Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    {z : Poly k N} (hz : z ∈ zeroIdeal L s) {δ : Ω} (hδ : δ ∈ L.sub (singleChart hj)) :
    ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * δ ∈
      Submodule.span (chartRing k x (singleChart hj)) {s} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coe_aeval_ratio_mul_mem_span» := P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mul_mem_span_1d57a849979c
