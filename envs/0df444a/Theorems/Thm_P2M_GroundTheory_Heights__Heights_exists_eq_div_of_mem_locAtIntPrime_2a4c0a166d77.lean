-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_eq_div_of_mem_locAtIntPrime_2a4c0a166d77
-- name    : P2M_GroundTheory_Heights__Heights_exists_eq_div_of_mem_locAtIntPrime_2a4c0a166d77
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:47.659694+00:00
-- url     : https://prove2.me/theorems/2956c5dd-ad8a-4705-89a6-1cb9b7ef69fa
-- title:
--   P2 M Ground Theory Heights  Heights exists eq div of mem loc At Int Prime 2a4c0a166d77: P2 M Ground Theory Heights  Heights exists eq div of mem loc At Int Prime 2a4c0a166d77
-- statement:
--   The P2 M Ground Theory Heights  Heights exists eq div of mem loc At Int Prime 2a4c0a166d77 construction uses the P2 M Ground Theory Heights  Heights exists eq div of mem loc At Int Prime 2a4c0a166d77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L40-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L40-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_exists_eq_div_of_mem_locAtIntPrime_2a4c0a166d77 [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : Subalgebra ℤ Ω) {u : Ω}
    (hu : u ∈ locAtIntPrime p A.toSubring) :
    ∃ a ∈ A, ∃ t : ℕ, ¬ p ∣ t ∧ u = a * (t : Ω)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_eq_div_of_mem_locAtIntPrime» := P2M_GroundTheory_Heights__Heights_exists_eq_div_of_mem_locAtIntPrime_2a4c0a166d77
