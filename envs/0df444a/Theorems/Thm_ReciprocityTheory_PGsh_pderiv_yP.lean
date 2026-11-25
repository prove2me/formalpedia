-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_pderiv_yP
-- name    : ReciprocityTheory.PGsh.pderiv_yP
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:09:33.085882+00:00
-- url     : https://prove2.me/theorems/a4c5df48-a073-4ebc-b648-512c11406af6
-- title:
--   PGsh: pderiv y P
-- statement:
--   The PGsh construction uses the pderiv y P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L303-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L303-L316

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

theorem ReciprocityTheory.PGsh.pderiv_yP (σ τ : Fin n → Fin n) (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S) :
    pderiv (σ j, j) (yP σ τ S) = yP σ τ (insert j S) := by sorry
