-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_union_split_d0b5eb59111d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_monos_union_split_d0b5eb59111d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:06.346497+00:00
-- url     : https://prove2.me/theorems/8c35e469-524f-40f7-a527-521eb70282b3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman monos union split d0b5eb59111d: P2 M Ground Theory Heights  Heights Kleiman monos union split d0b5eb59111d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman monos union split d0b5eb59111d construction uses the P2 M Ground Theory Heights  Heights Kleiman monos union split d0b5eb59111d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZeroIdealChart.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZeroIdealChart.lean#L22-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_monos_union_split_d0b5eb59111d {I K : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos (I ∪ K)) :
    ∃ u ∈ monos (S := S) I, ∃ v ∈ monos (S := S) K, u * v = s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«monos_union_split» := P2M_GroundTheory_Heights__Heights_Kleiman_monos_union_split_d0b5eb59111d
