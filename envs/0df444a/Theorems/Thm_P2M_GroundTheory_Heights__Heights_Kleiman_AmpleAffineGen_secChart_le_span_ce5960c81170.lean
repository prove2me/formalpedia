-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_le_span_ce5960c81170
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_le_span_ce5960c81170
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:58:33.044854+00:00
-- url     : https://prove2.me/theorems/d21fc279-dac3-4568-aadc-b367e56c8e25
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart le span ce5960c81170: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart le span ce5960c81170
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart le span ce5960c81170 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart le span ce5960c81170 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L262-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L262-L299

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_le_span_ce5960c81170 (Q H : LineBundle S x) (m b : ℕ) {h : Ω} (h0 : h ≠ 0) (J : Chart x)
    (hh : h ∈ (H.pow m).sub J) {G : Set Ω}
    (hG : Submodule.span (chartRing S x J) G = (Q.twist (H.pow b)).sub J) {z : Ω}
    (hz : z ∈ secChart Q.toSubSystem H.toSubSystem m b h J) :
    z ∈ Submodule.span (ampleSubalg H.toSubSystem m h J hh) G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«secChart_le_span» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_le_span_ce5960c81170
