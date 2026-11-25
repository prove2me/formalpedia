-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_algHom_ratio_self_39a1530ef58d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_algHom_ratio_self_39a1530ef58d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:30.132563+00:00
-- url     : https://prove2.me/theorems/19c91d32-b1a6-5775-abc5-4f419c2fb5fe
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman alg Hom ratio self 39a1530ef58d: P2 M Ground Theory Heights  Heights Kleiman alg Hom ratio self 39a1530ef58d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman alg Hom ratio self 39a1530ef58d construction uses the P2 M Ground Theory Heights  Heights Kleiman alg Hom ratio self 39a1530ef58d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L192-L195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_algHom_ratio_self_39a1530ef58d {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    (ψ : chartRing k x (singleChart hj) →ₐ[k] K') : ψ (ratio hj j) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«algHom_ratio_self» := P2M_GroundTheory_Heights__Heights_Kleiman_algHom_ratio_self_39a1530ef58d
