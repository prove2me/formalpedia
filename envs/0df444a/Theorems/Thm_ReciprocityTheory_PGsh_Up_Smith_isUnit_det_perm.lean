-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_isUnit_det_perm
-- name    : ReciprocityTheory.PGsh.Up.Smith.isUnit_det_perm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:16.523489+00:00
-- url     : https://prove2.me/theorems/4486516c-4144-5b29-981a-1acdee395447
-- title:
--   Smith: is Unit det perm
-- statement:
--   The Smith construction uses the is Unit det perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean#L95-L100

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

theorem ReciprocityTheory.PGsh.Up.Smith.isUnit_det_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) R).det := by sorry
