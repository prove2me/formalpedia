-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_eval_one_cayOp_pow
-- name    : ReciprocityTheory.PGsh.eval_one_cayOp_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:12.186794+00:00
-- url     : https://prove2.me/theorems/7004edfe-ee86-4aef-bc28-3f5c393830e1
-- title:
--   PGsh: eval one cay Op pow
-- statement:
--   The PGsh construction uses the eval one cay Op pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L411-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L411-L433

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

theorem ReciprocityTheory.PGsh.eval_one_cayOp_pow (s : ℕ) :
    eval onePt (cayOp n ℤ (cayDet n ℤ ^ s)) = ((∏ k ∈ range n, (s + k) : ℕ) : ℤ) := by sorry
