-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_aeval_div_pow_3ee1d0390a06
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_aeval_div_pow_3ee1d0390a06
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:00.204622+00:00
-- url     : https://prove2.me/theorems/49f2e70c-2f2e-49fb-899e-75db192b1306
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type aeval div pow 3ee1d0390a06: P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type aeval div pow 3ee1d0390a06
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type aeval div pow 3ee1d0390a06 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type aeval div pow 3ee1d0390a06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingFiniteType.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingFiniteType.lean#L19-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingFiniteType
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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_aeval_div_pow_3ee1d0390a06 {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (c : Ω) :
    aeval (fun i => x i / c) f = aeval x f / c ^ e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleRingFiniteType».«aeval_div_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_aeval_div_pow_3ee1d0390a06
