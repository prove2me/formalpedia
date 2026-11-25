-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_eig_pow_eq_one
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.eig_pow_eq_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:06:35.380731+00:00
-- url     : https://prove2.me/theorems/7f879361-afd2-53f3-94af-3cde0b83c1e9
-- title:
--   Frobenius Group Field: eig pow eq one
-- statement:
--   The Frobenius Group Field construction uses the eig pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigPowEqOne.lean#L27-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigPowEqOne.lean#L27-L40

import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.eig_pow_eq_one (hv : v.Integers R) {p : ℕ} [Fact p.Prime] {n : Type} [Fintype n] [DecidableEq n]
    [Algebra ℤ_[p] R] (N : Matrix n n ℤ_[p]) (e : Matrix n n R) (he : e ≠ 0) (x : R)
    (h : N.map (algebraMap ℤ_[p] R) * e = x • e) {m : ℕ} (hN : N ^ m = 1) : x ^ m = 1 := by sorry
