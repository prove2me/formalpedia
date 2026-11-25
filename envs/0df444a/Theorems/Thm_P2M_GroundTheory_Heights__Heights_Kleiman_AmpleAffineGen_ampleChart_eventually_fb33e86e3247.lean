-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_eventually_fb33e86e3247
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_eventually_fb33e86e3247
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:00:04.750606+00:00
-- url     : https://prove2.me/theorems/c5618790-1c7f-467d-a857-a1c3f680f7e1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart eventually fb33e86e3247: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart eventually fb33e86e3247
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart eventually fb33e86e3247 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart eventually fb33e86e3247 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L213-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L213-L222

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_eventually_fb33e86e3247 {H : SubSystem S x Ω} {m : ℕ} {h : Ω} {I : Chart x}
    (hh : h ∈ (H.pow m).sub I) {a : Ω} (ha : a ∈ ampleChart H m h I) :
    ∀ᶠ e in Filter.atTop, a * h ^ e ∈ (H.pow (m * e)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«ampleChart_eventually» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_eventually_fb33e86e3247
