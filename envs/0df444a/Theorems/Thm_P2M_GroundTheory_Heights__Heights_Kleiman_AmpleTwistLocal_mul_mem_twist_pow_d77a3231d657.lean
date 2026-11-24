-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_twist_pow_d77a3231d657
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_twist_pow_d77a3231d657
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:05.964245+00:00
-- url     : https://prove2.me/theorems/603aaec4-99dc-46b9-b671-6f47b5439430
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mul mem twist pow d77a3231d657: P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mul mem twist pow d77a3231d657
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mul mem twist pow d77a3231d657 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mul mem twist pow d77a3231d657 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleTwistLocal.lean#L65-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleTwistLocal.lean#L65-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmpleAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_twist_pow_d77a3231d657 (Q H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z w : Ω}
    (hz : z ∈ (Q.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (Q.twist (H.pow (c + d))).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleTwistLocal».«mul_mem_twist_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_twist_pow_d77a3231d657
