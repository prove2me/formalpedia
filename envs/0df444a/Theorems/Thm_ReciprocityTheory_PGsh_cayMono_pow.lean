-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_cayMono_pow
-- name    : ReciprocityTheory.PGsh.cayMono_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:22.681027+00:00
-- url     : https://prove2.me/theorems/a420cb21-3cc7-4cad-aff8-7ac679030789
-- title:
--   PGsh: cay Mono pow
-- statement:
--   The PGsh construction uses the cay Mono pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L363-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L363-L371

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

theorem ReciprocityTheory.PGsh.cayMono_pow (σ : Equiv.Perm (Fin n)) (s : ℕ) :
    cayMono n ℤ σ (cayDet n ℤ ^ s) = ∑ φ : Fin n → Fin s, ∏ k, fibOp σ φ k (cayDet n ℤ) := by sorry
