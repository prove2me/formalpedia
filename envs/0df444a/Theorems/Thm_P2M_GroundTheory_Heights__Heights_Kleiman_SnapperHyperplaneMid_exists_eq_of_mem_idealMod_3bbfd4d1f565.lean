-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_exists_eq_of_mem_idealMod_3bbfd4d1f565
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_exists_eq_of_mem_idealMod_3bbfd4d1f565
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:18.398605+00:00
-- url     : https://prove2.me/theorems/8d51a63a-252c-4a0b-b10e-be90179bacf3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid exists eq of mem ideal Mod 3bbfd4d1f565: P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid exists eq of mem ideal Mo
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid exists eq of mem ideal Mod 3bbfd4d1f565 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid exists eq of mem ideal Mod 3bbfd4d1f565 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L74-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L74-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid
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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_exists_eq_of_mem_idealMod_3bbfd4d1f565 {pp : Ideal (Poly k N)} {I : Chart x} {z : Ω} (hz : z ∈ idealMod pp I) :
    ∃ (g s : Poly k N) (e : ℕ), g ∈ pp ∧ s ∈ monos I.1 ∧ g.IsHomogeneous e ∧ s.IsHomogeneous e ∧
      z = aeval x g / aeval x s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperHyperplaneMid».«exists_eq_of_mem_idealMod» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_exists_eq_of_mem_idealMod_3bbfd4d1f565
