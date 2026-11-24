-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:30.948942+00:00
-- url     : https://prove2.me/theorems/dfb1ac0b-035c-469a-b41c-0bee0c0d4cd6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mul mem pow 768a0aeb472a: P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mul mem pow 768a0aeb472a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mul mem pow 768a0aeb472a construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mul mem pow 768a0aeb472a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleTwistLocal.lean#L32-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleTwistLocal.lean#L32-L53

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a (H : SubSystem S x Ω) (I : Chart x) {c : ℕ} {z : Ω}
    (hz : z ∈ (H.pow c).sub I) (d : ℕ) {w : Ω} (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (H.pow (c + d)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleTwistLocal».«mul_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a
