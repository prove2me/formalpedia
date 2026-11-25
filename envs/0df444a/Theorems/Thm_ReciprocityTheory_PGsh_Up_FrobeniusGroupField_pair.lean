-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_pair
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.pair
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:19.311616+00:00
-- url     : https://prove2.me/theorems/63cc8d33-048d-4c8c-a44e-07701adcb999
-- title:
--   Frobenius Group Field: pair
-- statement:
--   The Frobenius Group Field construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SgAlgebraMap.lean#L144-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SgAlgebraMap.lean#L144-L200

import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis
import Definitions.Def_ReciprocityTheory_DualLattices_SgAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix Polynomial
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.pair (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hv : v.Integers R)
    (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (a : O) (t : ℕ)
    (i j : ι) (hi : εT i ≠ 0) (hj : εT j ≠ 0) (h : res hv (sg j a) ≠ res hv (sg i a) ^ p ^ t) :
    ∃ (b : O) (m : ℕ), 0 < m ∧ ¬ p ∣ m ∧ ρ b ^ m = 1 ∧
      res hv (sg j b) ≠ res hv (sg i b) ^ p ^ t := by sorry
