-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_det_blockOne_alt
-- name    : ReciprocityTheory.PGsh.Up.Smith.det_blockOne_alt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:17.772086+00:00
-- url     : https://prove2.me/theorems/5812f610-47d1-511c-86a7-a9becfb341ff
-- title:
--   Smith: det block One alt
-- statement:
--   The Smith construction uses the det block One alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean#L70-L74

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

theorem ReciprocityTheory.PGsh.Up.Smith.det_blockOne_alt {N : ℕ} (P : Matrix (Fin N) (Fin N) R) : (bd1 P).det = P.det := by sorry
