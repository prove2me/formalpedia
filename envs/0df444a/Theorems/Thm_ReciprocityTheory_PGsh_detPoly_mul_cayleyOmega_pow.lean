-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_detPoly_mul_cayleyOmega_pow
-- name    : ReciprocityTheory.PGsh.detPoly_mul_cayleyOmega_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:10:20.803043+00:00
-- url     : https://prove2.me/theorems/39c95247-5c37-4076-941c-f8751b38879d
-- title:
--   PGsh: det Poly mul cayley Omega pow
-- statement:
--   The PGsh construction uses the det Poly mul cayley Omega pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L215-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L215-L227

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

theorem ReciprocityTheory.PGsh.detPoly_mul_cayleyOmega_pow (s : ℕ) :
    cayDet n ℤ * cayOp n ℤ (cayDet n ℤ ^ s) =
      C (eval onePt (cayOp n ℤ (cayDet n ℤ ^ s))) * cayDet n ℤ ^ s := by sorry
