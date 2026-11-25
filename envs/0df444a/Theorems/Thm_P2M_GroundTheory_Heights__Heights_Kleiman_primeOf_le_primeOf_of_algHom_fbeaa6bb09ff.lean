-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_le_primeOf_of_algHom_fbeaa6bb09ff
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_le_primeOf_of_algHom_fbeaa6bb09ff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:04:34.500319+00:00
-- url     : https://prove2.me/theorems/5ec6818d-8295-5d1c-a354-f6c52cc81ca0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman prime Of le prime Of of alg Hom fbeaa6bb09ff: P2 M Ground Theory Heights  Heights Kleiman prime Of le prime Of of alg Hom fbeaa6bb09ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman prime Of le prime Of of alg Hom fbeaa6bb09ff construction uses the P2 M Ground Theory Heights  Heights Kleiman prime Of le prime Of of alg Hom fbeaa6bb09ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L167-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L167-L190

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_le_primeOf_of_algHom_fbeaa6bb09ff {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    (ψ : chartRing k x (singleChart hj) →ₐ[k] K') :
    primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«primeOf_le_primeOf_of_algHom» := P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_le_primeOf_of_algHom_fbeaa6bb09ff
