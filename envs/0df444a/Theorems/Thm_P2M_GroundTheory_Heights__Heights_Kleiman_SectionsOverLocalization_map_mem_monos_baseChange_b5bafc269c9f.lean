-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_map_mem_monos_baseChange_b5bafc269c9f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_map_mem_monos_baseChange_b5bafc269c9f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:15:18.842915+00:00
-- url     : https://prove2.me/theorems/7a0a65ef-3db6-4e69-8a2d-8d6e1b6bbed6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization map mem monos base Change b5bafc269c9f: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization map mem monos base
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization map mem monos base Change b5bafc269c9f construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization map mem monos base Change b5bafc269c9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L19-L27

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
omit [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_map_mem_monos_baseChange_b5bafc269c9f {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    map (algebraMap S O) s ∈ monos (S := O) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«map_mem_monos_baseChange» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_map_mem_monos_baseChange_b5bafc269c9f
