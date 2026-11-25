-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_pow_mem_pow_ef4744dee65c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mul_pow_mem_pow_ef4744dee65c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:06.642789+00:00
-- url     : https://prove2.me/theorems/04160455-e453-4300-819e-51e529441e83
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mul pow mem pow ef4744dee65c: P2 M Ground Theory Heights  Heights Kleiman mul pow mem pow ef4744dee65c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mul pow mem pow ef4744dee65c construction uses the P2 M Ground Theory Heights  Heights Kleiman mul pow mem pow ef4744dee65c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L23-L29

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mul_pow_mem_pow_ef4744dee65c (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) (j : ℕ) : a * q ^ j ∈ (Q.pow (m + j)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mul_pow_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_mul_pow_mem_pow_ef4744dee65c
