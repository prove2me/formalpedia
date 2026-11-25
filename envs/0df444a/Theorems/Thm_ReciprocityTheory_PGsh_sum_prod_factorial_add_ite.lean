-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_sum_prod_factorial_add_ite
-- name    : ReciprocityTheory.PGsh.sum_prod_factorial_add_ite
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:07.813678+00:00
-- url     : https://prove2.me/theorems/c772277e-be3e-47b7-a36d-0590b8a04dc8
-- title:
--   PGsh: sum prod factorial add ite
-- statement:
--   The PGsh construction uses the sum prod factorial add ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L379-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L379-L393

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

theorem ReciprocityTheory.PGsh.sum_prod_factorial_add_ite {s : ℕ} (c : Fin s → ℕ) :
    ∑ k₀, ∏ k, (c k + if k₀ = k then 1 else 0).factorial =
      (∏ k, (c k).factorial) * (∑ k, c k + s) := by sorry
