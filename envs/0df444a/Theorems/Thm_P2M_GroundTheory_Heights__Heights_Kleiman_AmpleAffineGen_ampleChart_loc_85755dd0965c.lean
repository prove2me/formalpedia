-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_loc_85755dd0965c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_loc_85755dd0965c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:10:41.205465+00:00
-- url     : https://prove2.me/theorems/2640305b-d6a6-5471-8c40-84e59904ad0f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart loc 85755dd0965c: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart loc 85755dd0965c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart loc 85755dd0965c construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen ample Chart loc 85755dd0965c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L224-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L224-L230

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_loc_85755dd0965c (H : LineBundle S x) {m : ℕ} {h : Ω} (I J : Chart x) {a : Ω}
    (ha : a ∈ ampleChart H.toSubSystem m h (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * a ∈ ampleChart H.toSubSystem m h I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«ampleChart_loc» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_loc_85755dd0965c
