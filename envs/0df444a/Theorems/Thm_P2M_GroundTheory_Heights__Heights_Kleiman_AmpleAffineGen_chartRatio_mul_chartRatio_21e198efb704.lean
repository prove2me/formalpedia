-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mul_chartRatio_21e198efb704
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mul_chartRatio_21e198efb704
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:36.97963+00:00
-- url     : https://prove2.me/theorems/ca99ed01-a523-473c-be56-ea96623abedc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen chart Ratio mul chart Ratio 21e198efb704: P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen chart Ratio mul chart Ratio 21e198ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen chart Ratio mul chart Ratio 21e198efb704 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Affine Gen chart Ratio mul chart Ratio 21e198efb704 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleAffineGen.lean#L33-L35

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mul_chartRatio_21e198efb704 (I J : Chart x) : chartRatio J I * chartRatio I J = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleAffineGen».«chartRatio_mul_chartRatio» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mul_chartRatio_21e198efb704
