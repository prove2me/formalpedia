-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_loc_90c900bcc943
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_loc_90c900bcc943
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:54.42637+00:00
-- url     : https://prove2.me/theorems/0d527790-ea29-5e92-a971-37b404600780
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart loc 90c900bcc943: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart loc 90c900bcc943
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart loc 90c900bcc943 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart loc 90c900bcc943 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L254-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L254-L260

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_loc_90c900bcc943 (Q H : LineBundle S x) {m b : ℕ} {h : Ω} (I J : Chart x) {z : Ω}
    (hz : z ∈ secChart Q.toSubSystem H.toSubSystem m b h (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * z ∈ secChart Q.toSubSystem H.toSubSystem m b h I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«secChart_loc» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_loc_90c900bcc943
