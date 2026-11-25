-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_eval_fibOp_cayDet
-- name    : ReciprocityTheory.PGsh.eval_fibOp_cayDet
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:29.154034+00:00
-- url     : https://prove2.me/theorems/d189a778-2e4a-4cd2-b1db-5526e71cf4c7
-- title:
--   PGsh: eval fib Op cay Det
-- statement:
--   The PGsh construction uses the eval fib Op cay Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L339-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L339-L361

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

theorem ReciprocityTheory.PGsh.eval_fibOp_cayDet (σ : Fin n → Fin n) {s : ℕ} (φ : Fin n → Fin s) (k : Fin s) :
    eval onePt (fibOp σ φ k (cayDet n ℤ)) =
      (funMat fun b => if φ b = k then σ b else b).det := by sorry
