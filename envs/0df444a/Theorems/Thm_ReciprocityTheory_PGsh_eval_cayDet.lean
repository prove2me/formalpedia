-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_eval_cayDet
-- name    : ReciprocityTheory.PGsh.eval_cayDet
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:35.136809+00:00
-- url     : https://prove2.me/theorems/3e50f04e-499d-40d8-8e77-3c4054917005
-- title:
--   PGsh: eval cay Det
-- statement:
--   The PGsh construction uses the eval cay Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L207-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L207-L213

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

theorem ReciprocityTheory.PGsh.eval_cayDet (x : Fin n × Fin n → ℤ) :
    eval x (cayDet n ℤ) = (Matrix.of fun i j => x (i, j)).det := by sorry
