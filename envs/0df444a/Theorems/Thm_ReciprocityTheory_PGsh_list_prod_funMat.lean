-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_list_prod_funMat
-- name    : ReciprocityTheory.PGsh.list_prod_funMat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:10.206936+00:00
-- url     : https://prove2.me/theorems/aa32d36d-7b17-4e55-8085-638cb8d0a6d6
-- title:
--   PGsh: list prod fun Mat
-- statement:
--   The PGsh construction uses the list prod fun Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L260-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L260-L274

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

theorem ReciprocityTheory.PGsh.list_prod_funMat {s : ℕ} (σ : Equiv.Perm (Fin n)) (φ : Fin n → Fin s)
    (hσ : ∀ b, φ (σ b) = φ b) (L : List (Fin s)) (hL : L.Nodup) :
    (L.map fun k => funMat (fun b => if φ b = k then σ b else b)).prod =
      funMat (fun b => if φ b ∈ L then σ b else b) := by sorry
