-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_sub_le_950687240963
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_sub_le_950687240963
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:23.488142+00:00
-- url     : https://prove2.me/theorems/07bf40e7-bc3d-4b68-830e-4fe32d2f6c90
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys sub le 950687240963: P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys sub le 950687240963
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys sub le 950687240963 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys sub le 950687240963 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L55-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_sub_le_950687240963 (Q : SubSystem S x Ω) (J : Ideal (Poly S N)) (I : Chart x) :
    (Q.twist (idealSys x J)).sub I ≤ Q.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twist_idealSys_sub_le» := P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_sub_le_950687240963
