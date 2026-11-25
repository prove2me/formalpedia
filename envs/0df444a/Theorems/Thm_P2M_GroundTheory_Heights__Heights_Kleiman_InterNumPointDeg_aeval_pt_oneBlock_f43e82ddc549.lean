-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_oneBlock_f43e82ddc549
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_oneBlock_f43e82ddc549
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:29:22.93358+00:00
-- url     : https://prove2.me/theorems/2fde0d02-e797-57de-9a94-29b6d68a7b39
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg aeval pt one Block f43e82ddc549: P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg aeval pt one Block f43e82ddc549
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg aeval pt one Block f43e82ddc549 construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg aeval pt one Block f43e82ddc549 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean#L51-L59

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_oneBlock_f43e82ddc549 (f : OneRing k N) :
    aeval (pt.{u, w} pp) (oneBlock (S := k) (N := N) f) = coneHom pp f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumPointDeg».«aeval_pt_oneBlock» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_oneBlock_f43e82ddc549
