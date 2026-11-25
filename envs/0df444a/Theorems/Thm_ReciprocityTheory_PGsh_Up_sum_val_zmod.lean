-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_sum_val_zmod
-- name    : ReciprocityTheory.PGsh.Up.sum_val_zmod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:08:35.000388+00:00
-- url     : https://prove2.me/theorems/a4cf9eaf-abe8-5d5b-9aea-15ba0e47545b
-- title:
--   Up: sum val zmod
-- statement:
--   The Up construction uses the sum val zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumValCoord.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumValCoord.lean#L10-L23

import Definitions.Def_ReciprocityTheory_DualLattices_MonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_SumValCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up

theorem ReciprocityTheory.PGsh.Up.sum_val_zmod (p : ℕ) [Fact p.Prime] : ∑ a : ZMod p, a.val = p * (p - 1) / 2 := by sorry
