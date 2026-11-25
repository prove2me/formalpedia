-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_map_mem_monos_1c3de4584cdf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_map_mem_monos_1c3de4584cdf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:23:22.688958+00:00
-- url     : https://prove2.me/theorems/43249121-d9e5-4d79-9907-9370a3daa0a1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman map mem monos 1c3de4584cdf: P2 M Ground Theory Heights  Heights Kleiman map mem monos 1c3de4584cdf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman map mem monos 1c3de4584cdf construction uses the P2 M Ground Theory Heights  Heights Kleiman map mem monos 1c3de4584cdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExtendTwist.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExtendTwist.lean#L20-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
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
open scoped Pointwise
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
omit [IsScalarTower S F Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_map_mem_monos_1c3de4584cdf {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    map (algebraMap S F) s ∈ monos (S := F) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«map_mem_monos» := P2M_GroundTheory_Heights__Heights_Kleiman_map_mem_monos_1c3de4584cdf
