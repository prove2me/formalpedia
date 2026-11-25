-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_eval_onePt_linSub
-- name    : ReciprocityTheory.PGsh.eval_onePt_linSub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:04.340899+00:00
-- url     : https://prove2.me/theorems/baf230f5-939b-5d31-b4b8-52bd6a1bb9ab
-- title:
--   PGsh: eval one Pt lin Sub
-- statement:
--   The PGsh construction uses the eval one Pt lin Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L198-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L198-L205

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

theorem ReciprocityTheory.PGsh.eval_onePt_linSub (x : Fin n × Fin n → ℤ) (p : MvPolynomial (Fin n × Fin n) ℤ) :
    eval onePt (linSub (Matrix.of fun i j => x (i, j)) p) = eval x p := by sorry
