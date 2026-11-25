-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mem_chartRing_of_mem_zero_d23a951cca05
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mem_chartRing_of_mem_zero_d23a951cca05
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:26:55.759775+00:00
-- url     : https://prove2.me/theorems/68a7e8d3-4946-46c5-a4ff-a8cdc9650a10
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mem chart Ring of mem zero d23a951cca05: P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mem chart Ring of mem zero d23a951c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mem chart Ring of mem zero d23a951cca05 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Twist Local mem chart Ring of mem zero d23a951cca05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleTwistLocal.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleTwistLocal.lean#L19-L30

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mem_chartRing_of_mem_zero_d23a951cca05 {I : Chart x} {q : Ω} (hq : q ∈ twistMod S x 0 I) :
    q ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleTwistLocal».«mem_chartRing_of_mem_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mem_chartRing_of_mem_zero_d23a951cca05
