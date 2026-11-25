-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_tensorSub_9c5ba360f068
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_tensorSub_9c5ba360f068
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:07:31.575104+00:00
-- url     : https://prove2.me/theorems/b5957ae2-16e9-407e-8c42-4069cd7cf461
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change tensor Sub 9c5ba360f068: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change tensor Su
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change tensor Sub 9c5ba360f068 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization base Change tensor Sub 9c5ba360f068 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L81-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L81-L94

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_tensorSub_9c5ba360f068 {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub (fun i => (L i).baseChange O) T = (tensorSub L T).baseChange O := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«baseChange_tensorSub» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_tensorSub_9c5ba360f068
