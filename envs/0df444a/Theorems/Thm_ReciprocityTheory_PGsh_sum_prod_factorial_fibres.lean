-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_sum_prod_factorial_fibres
-- name    : ReciprocityTheory.PGsh.sum_prod_factorial_fibres
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:57.584611+00:00
-- url     : https://prove2.me/theorems/403ba210-ed8c-46cd-b8ad-18e312580dfd
-- title:
--   PGsh: sum prod factorial fibres
-- statement:
--   The PGsh construction uses the sum prod factorial fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L395-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L395-L409

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

theorem ReciprocityTheory.PGsh.sum_prod_factorial_fibres (s : ℕ) : ∀ m : ℕ,
    ∑ φ : Fin m → Fin s, ∏ k, (#{a | φ a = k}).factorial = ∏ j ∈ range m, (s + j)
  := by sorry
