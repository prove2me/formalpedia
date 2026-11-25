-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_blockForm_e1c52d6b018e
-- name    : P2M_GroundTheory_Heights__Heights_exists_blockForm_e1c52d6b018e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:04.730816+00:00
-- url     : https://prove2.me/theorems/0bce5f8b-c8da-47f5-90cb-ad21ed421ea8
-- title:
--   P2 M Ground Theory Heights  Heights exists block Form e1c52d6b018e: P2 M Ground Theory Heights  Heights exists block Form e1c52d6b018e
-- statement:
--   The P2 M Ground Theory Heights  Heights exists block Form e1c52d6b018e construction uses the P2 M Ground Theory Heights  Heights exists block Form e1c52d6b018e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VarsSubsetRangeBlockIncl.lean#L48-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VarsSubsetRangeBlockIncl.lean#L48-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VarsSubsetRangeBlockIncl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_exists_blockForm_e1c52d6b018e (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    ∃ f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ n k₀)) f' (fun _ ↦ m) ∧
        rename (blockIncl k₀) f' = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_blockForm» := P2M_GroundTheory_Heights__Heights_exists_blockForm_e1c52d6b018e
