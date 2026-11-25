-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twistSys_73f82ae90cab
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twistSys_73f82ae90cab
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:15:09.663971+00:00
-- url     : https://prove2.me/theorems/e5c00beb-d441-5e39-93db-e9ade773672e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change twist Sys 73f82ae90cab: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change twist Sys
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change twist Sys 73f82ae90cab construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change twist Sys 73f82ae90cab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L55-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
open scoped Pointwise
noncomputable section
variable {S : Type*} [CommRing S] {O : Type*} [CommRing O] [Algebra S O] {Ω : Type*} [Field Ω]
  [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twistSys_73f82ae90cab (c : ℤ) : (twistSys S x c).baseChange O = twistSys O x c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«baseChange_twistSys» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twistSys_73f82ae90cab
