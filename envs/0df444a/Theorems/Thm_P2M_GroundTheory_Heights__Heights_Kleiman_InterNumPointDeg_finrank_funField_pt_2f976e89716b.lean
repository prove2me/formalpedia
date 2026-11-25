-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_finrank_funField_pt_2f976e89716b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_finrank_funField_pt_2f976e89716b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:38.656815+00:00
-- url     : https://prove2.me/theorems/096977d8-8ec1-433c-be21-f7b8e307b665
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg finrank fun Field pt 2f976e89716b: P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg finrank fun Field pt 2f976e89716b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg finrank fun Field pt 2f976e89716b construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg finrank fun Field pt 2f976e89716b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean#L94-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean#L94-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumPointDeg
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
variable {k : Type u} [Field k] {N : ℕ}
variable [Small.{w} k] (pp : Ideal (Poly k N)) [pp.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_finrank_funField_pt_2f976e89716b (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    Module.finrank k (funField (k := k) (pt.{u, w} pp)) =
      FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumPointDeg».«finrank_funField_pt» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_finrank_funField_pt_2f976e89716b
