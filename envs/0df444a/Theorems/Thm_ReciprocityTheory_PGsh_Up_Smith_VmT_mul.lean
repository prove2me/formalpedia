-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_VmT_mul
-- name    : ReciprocityTheory.PGsh.Up.Smith.VmT_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:40.131999+00:00
-- url     : https://prove2.me/theorems/3c2f99ce-34e3-5a44-8b33-657690d43f5e
-- title:
--   Smith: Vm T mul
-- statement:
--   The Smith construction uses the Vm T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BlockOneMulMulBlockOne.lean#L40-L48

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

theorem ReciprocityTheory.PGsh.Up.Smith.VmT_mul {N n : ℕ} (j0 : Fin (N + 1)) (u : Fin (N + 1) → R) (Y : Matrix (Fin (N + 1)) (Fin n) R)
    (k : Fin (N + 1)) (l : Fin n) :
    ((Vm j0 u)ᵀ * Y) k l = if k = j0 then Y j0 l else Y k l - u k * Y j0 l := by sorry
