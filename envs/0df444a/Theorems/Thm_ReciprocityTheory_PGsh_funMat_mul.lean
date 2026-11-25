-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_funMat_mul
-- name    : ReciprocityTheory.PGsh.funMat_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:18.556461+00:00
-- url     : https://prove2.me/theorems/534c22f6-e2f9-54a9-bf4e-f73d3a27130b
-- title:
--   PGsh: fun Mat mul
-- statement:
--   The PGsh construction uses the fun Mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L240-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L240-L244

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

theorem ReciprocityTheory.PGsh.funMat_mul (ρ ρ' : Fin n → Fin n) : funMat ρ * funMat ρ' = funMat (ρ ∘ ρ') := by sorry
