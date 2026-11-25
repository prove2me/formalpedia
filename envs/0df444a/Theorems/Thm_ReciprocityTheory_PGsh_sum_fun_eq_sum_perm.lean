-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_sum_fun_eq_sum_perm
-- name    : ReciprocityTheory.PGsh.sum_fun_eq_sum_perm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:05.651693+00:00
-- url     : https://prove2.me/theorems/dafdcfa2-02b3-4606-b7d4-3eff94cb635d
-- title:
--   PGsh: sum fun eq sum perm
-- statement:
--   The PGsh construction uses the sum fun eq sum perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L134-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L134-L149

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

theorem ReciprocityTheory.PGsh.sum_fun_eq_sum_perm {M : Type*} [AddCommMonoid M] (F : (Fin n → Fin n) → M)
    (h : ∀ τ, ¬ Function.Injective τ → F τ = 0) :
    ∑ τ, F τ = ∑ e : Equiv.Perm (Fin n), F e := by sorry
