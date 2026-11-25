-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_mono_6765e17e9241
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_mono_6765e17e9241
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:10:48.259548+00:00
-- url     : https://prove2.me/theorems/5abce890-667f-511a-a0b9-df3609ba0471
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart mono 6765e17e9241: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart mono 6765e17e9241
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart mono 6765e17e9241 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart mono 6765e17e9241 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L208-L211

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_mono_6765e17e9241 {H : SubSystem S x Ω} {m : ℕ} {h : Ω} {I K : Chart x} (hIK : I.1 ⊆ K.1)
    {a : Ω} (ha : a ∈ ampleChart H m h I) : a ∈ ampleChart H m h K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«ampleChart_mono» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_mono_6765e17e9241
