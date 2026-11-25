-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_prod_det_funMat
-- name    : ReciprocityTheory.PGsh.prod_det_funMat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:09:21.44791+00:00
-- url     : https://prove2.me/theorems/610d778d-aa76-4050-89ab-ec429485cb72
-- title:
--   PGsh: prod det fun Mat
-- statement:
--   The PGsh construction uses the prod det fun Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L276-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L276-L298

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

theorem ReciprocityTheory.PGsh.prod_det_funMat {s : ℕ} (σ : Equiv.Perm (Fin n)) (φ : Fin n → Fin s) :
    ∏ k, (funMat (fun b => if φ b = k then σ b else b)).det =
      if φ ∘ σ = φ then (Equiv.Perm.sign σ : ℤ) else 0 := by sorry
