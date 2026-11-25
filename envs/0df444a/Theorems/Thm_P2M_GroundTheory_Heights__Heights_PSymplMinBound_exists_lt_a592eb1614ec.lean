-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinBound_exists_lt_a592eb1614ec
-- name    : P2M_GroundTheory_Heights__Heights_PSymplMinBound_exists_lt_a592eb1614ec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:15.592997+00:00
-- url     : https://prove2.me/theorems/34d9e671-a127-4338-8bd5-e0f36829e7be
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Min Bound exists lt a592eb1614ec: P2 M Ground Theory Heights  Heights PSympl Min Bound exists lt a592eb1614ec
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Min Bound exists lt a592eb1614ec construction uses the P2 M Ground Theory Heights  Heights PSympl Min Bound exists lt a592eb1614ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinBound.lean#L20-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplMinBound.lean#L20-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinBound
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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplMinBound

theorem P2M_GroundTheory_Heights__Heights_PSymplMinBound_exists_lt_a592eb1614ec (h2 : SymplMinkowskiBox.Statement) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (O : Matrix ι ι ℝ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (hO : |O.det| = 1)
    (hprod : ∏ i, lam i = 1) (c : ℝ) (hc : 1 < c) :
    ∃ v : ι → ℤ, v ≠ 0 ∧
      ∑ i, lam i * (O *ᵥ intVec v) i ^ 2 < (Fintype.card ι : ℝ) * c ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplMinBound».«exists_lt» := P2M_GroundTheory_Heights__Heights_PSymplMinBound_exists_lt_a592eb1614ec
