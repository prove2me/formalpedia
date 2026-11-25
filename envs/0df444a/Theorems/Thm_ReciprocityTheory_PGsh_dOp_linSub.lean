-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_dOp_linSub
-- name    : ReciprocityTheory.PGsh.dOp_linSub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:40.009411+00:00
-- url     : https://prove2.me/theorems/0e6b7240-0637-4bce-947d-7f5db022fa6f
-- title:
--   PGsh: d Op lin Sub
-- statement:
--   The PGsh construction uses the d Op lin Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L111-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L111-L128

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
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.PGsh.dOp_linSub {m : ℕ} (g : Matrix (Fin n) (Fin n) R) (r c : Fin m → Fin n)
    (q : MvPolynomial (Fin n × Fin n) R) :
    dOp r c (linSub g q) =
      ∑ τ : Fin m → Fin n, C (∏ t, g (τ t) (r t)) * linSub g (dOp τ c q) := by sorry
