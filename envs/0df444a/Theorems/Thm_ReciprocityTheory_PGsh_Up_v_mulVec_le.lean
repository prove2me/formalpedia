-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_v_mulVec_le
-- name    : ReciprocityTheory.PGsh.Up.v_mulVec_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:05.992951+00:00
-- url     : https://prove2.me/theorems/b0e5a776-b28d-5d8a-b0a7-d32640c86782
-- title:
--   Up: v mul Vec le
-- statement:
--   The Up construction uses the v mul Vec le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLatInvMulVec.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLatInvMulVec.lean#L39-L44

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsUnitMinor
import Definitions.Def_ReciprocityTheory_DualLattices_SumLatInvMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem ReciprocityTheory.PGsh.Up.v_mulVec_le {m k : Type} [Fintype k] (P : Matrix m k C) (x : k → C)
    (hP : ∀ i j, v (P i j) ≤ 1) (hx : ∀ j, v (x j) ≤ 1) (i : m) : v ((P *ᵥ x) i) ≤ 1 := by sorry
