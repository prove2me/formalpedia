-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_pow_succ_8a28807f43b3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_pow_succ_8a28807f43b3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:41.856954+00:00
-- url     : https://prove2.me/theorems/c0ad1d6a-afa4-4f16-b5b5-b130963f8e7c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mul mem pow succ 8a28807f43b3: P2 M Ground Theory Heights  Heights Kleiman mul mem pow succ 8a28807f43b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mul mem pow succ 8a28807f43b3 construction uses the P2 M Ground Theory Heights  Heights Kleiman mul mem pow succ 8a28807f43b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L19-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop
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
open MvPolynomial Filter
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_pow_succ_8a28807f43b3 (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) : a * q ∈ (Q.pow (m + 1)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mul_mem_pow_succ» := P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_pow_succ_8a28807f43b3
