-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mem_idealMod_2810c4e8df36
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mem_idealMod_2810c4e8df36
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:01:22.735602+00:00
-- url     : https://prove2.me/theorems/ee3b8586-44c0-40e0-8841-64e953b99265
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio mem ideal Mod 2810c4e8df36: P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio mem ideal Mod 2810c4e8df36
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio mem ideal Mod 2810c4e8df36 construction uses the P2 M Ground Theory Heights  Heights Kleiman coe aeval ratio mem ideal Mod 2810c4e8df36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutNonempty.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutNonempty.lean#L18-L28

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mem_idealMod_2810c4e8df36 {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) {j : Fin (N + 1)} (hj : x j ≠ 0)
    {p : Poly k N} (hp : p ∈ pp) :
    ((aeval (ratio (S := k) hj) p : chartRing k x (singleChart hj)) : Ω) ∈
      idealMod (x := x) pp (singleChart hj) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coe_aeval_ratio_mem_idealMod» := P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mem_idealMod_2810c4e8df36
