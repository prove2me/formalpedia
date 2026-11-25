-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_piv_zero
-- name    : ReciprocityTheory.PGsh.Up.Smith.piv_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:14.850149+00:00
-- url     : https://prove2.me/theorems/3d5ef959-badc-40f9-b1a3-60296b2c8b49
-- title:
--   Smith: piv zero
-- statement:
--   The Smith construction uses the piv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean#L53-L54

import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.PGsh.Up.Smith.piv_zero {N : ℕ} (i0 : Fin (N + 1)) : piv i0 0 = i0 := by sorry
