-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_mono_f2443a5d1b14
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_mono_f2443a5d1b14
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:58:41.995625+00:00
-- url     : https://prove2.me/theorems/06faab63-dc05-4432-95ea-0deac49c4192
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart mono f2443a5d1b14: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart mono f2443a5d1b14
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart mono f2443a5d1b14 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart mono f2443a5d1b14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L245-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L245-L248

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_mono_f2443a5d1b14 {Q H : SubSystem S x Ω} {m b : ℕ} {h : Ω} {I K : Chart x} (hIK : I.1 ⊆ K.1)
    {z : Ω} (hz : z ∈ secChart Q H m b h I) : z ∈ secChart Q H m b h K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«secChart_mono» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_mono_f2443a5d1b14
