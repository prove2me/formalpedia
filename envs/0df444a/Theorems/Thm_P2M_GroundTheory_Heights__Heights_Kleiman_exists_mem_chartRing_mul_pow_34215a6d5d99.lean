-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_mem_chartRing_mul_pow_34215a6d5d99
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_mem_chartRing_mul_pow_34215a6d5d99
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:05:25.458908+00:00
-- url     : https://prove2.me/theorems/9d16e89f-e7bc-55f0-bb55-002628216496
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists mem chart Ring mul pow 34215a6d5d99: P2 M Ground Theory Heights  Heights Kleiman exists mem chart Ring mul pow 34215a6d5d99
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists mem chart Ring mul pow 34215a6d5d99 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists mem chart Ring mul pow 34215a6d5d99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L38-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L38-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_mem_chartRing_mul_pow_34215a6d5d99 (I J : Chart x) {c : Ω} (hc : c ∈ chartRing k x J) :
    ∃ (c' : Ω) (m : ℕ), c' ∈ chartRing k x I ∧
      c = c' * (xProd I ^ J.1.card / xProd J ^ I.1.card) ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_mem_chartRing_mul_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_mem_chartRing_mul_pow_34215a6d5d99
