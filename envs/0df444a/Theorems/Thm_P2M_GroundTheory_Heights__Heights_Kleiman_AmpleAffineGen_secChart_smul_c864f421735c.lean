-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_smul_c864f421735c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_smul_c864f421735c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:58:23.089565+00:00
-- url     : https://prove2.me/theorems/a201ee23-fa67-5a4c-a9e8-cdabc6787e26
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart smul c864f421735c: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart smul c864f421735c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart smul c864f421735c construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen sec Chart smul c864f421735c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L235-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L235-L243

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_smul_c864f421735c {Q H : SubSystem S x Ω} {m b : ℕ} {h : Ω} {I : Chart x} {a z : Ω}
    (ha : a ∈ ampleChart H m h I) (hz : z ∈ secChart Q H m b h I) : a * z ∈ secChart Q H m b h I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«secChart_smul» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_smul_c864f421735c
