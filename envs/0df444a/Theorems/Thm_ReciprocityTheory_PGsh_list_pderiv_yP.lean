-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_list_pderiv_yP
-- name    : ReciprocityTheory.PGsh.list_pderiv_yP
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:06.827034+00:00
-- url     : https://prove2.me/theorems/a87c6189-5c20-45ee-b580-14e6114112e2
-- title:
--   PGsh: list pderiv y P
-- statement:
--   The PGsh construction uses the list pderiv y P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L318-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L318-L332

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

theorem ReciprocityTheory.PGsh.list_pderiv_yP (σ τ : Fin n → Fin n) (l : List (Fin n)) (hl : l.Nodup)
    (S : Finset (Fin n)) (hS : ∀ j ∈ l, j ∉ S) :
    (l.map fun j => ((pderiv (σ j, j) : Derivation ℤ _ _) :
      MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℤ)).prod (yP σ τ S) =
      yP σ τ (S ∪ l.toFinset) := by sorry
