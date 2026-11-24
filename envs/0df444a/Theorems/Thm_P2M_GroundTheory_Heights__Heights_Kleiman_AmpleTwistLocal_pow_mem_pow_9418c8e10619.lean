-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:42.012016+00:00
-- url     : https://prove2.me/theorems/b13ebf82-12d1-43c6-bb3f-e3cdd7d57e88
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local pow mem pow 9418c8e10619: P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local pow mem pow 9418c8e10619
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local pow mem pow 9418c8e10619 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local pow mem pow 9418c8e10619 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleTwistLocal.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleTwistLocal.lean#L55-L63

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619 (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {h : Ω}
    (hh : h ∈ (H.pow m).sub I) (n : ℕ) : h ^ n ∈ (H.pow (m * n)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleTwistLocal».«pow_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619
