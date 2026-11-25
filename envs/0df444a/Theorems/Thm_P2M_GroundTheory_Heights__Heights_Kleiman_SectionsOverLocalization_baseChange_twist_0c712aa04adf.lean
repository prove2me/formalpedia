-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twist_0c712aa04adf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twist_0c712aa04adf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:16:38.179184+00:00
-- url     : https://prove2.me/theorems/bc969aa6-38fe-5c06-834b-d6d49799fce9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change twist 0c712aa04adf: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change twist 0c712aa0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change twist 0c712aa04adf construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change twist 0c712aa04adf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L63-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L63-L79

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
omit [Algebra S O] [IsScalarTower S O Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twist_0c712aa04adf (Q R : SubSystem S x Ω) :
    (Q.twist R).baseChange O = (Q.baseChange O).twist (R.baseChange O) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«baseChange_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twist_0c712aa04adf
