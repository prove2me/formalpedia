-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_cayley_int_succ
-- name    : ReciprocityTheory.PGsh.cayley_int_succ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:20.844904+00:00
-- url     : https://prove2.me/theorems/0334b389-3d2e-5d7f-b72d-f9d963835b6f
-- title:
--   PGsh: cayley int succ
-- statement:
--   The PGsh construction uses the cayley int succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L229-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L229-L235

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}

theorem ReciprocityTheory.PGsh.cayley_int_succ (s : ℕ) :
    cayOp n ℤ (cayDet n ℤ ^ (s + 1)) =
      C (eval onePt (cayOp n ℤ (cayDet n ℤ ^ (s + 1)))) * cayDet n ℤ ^ s := by sorry
