-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_sg_aeval
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.sg_aeval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:21.699948+00:00
-- url     : https://prove2.me/theorems/2318098e-5a4b-48fb-9125-d429c992daf8
-- title:
--   Frobenius Group Field: sg aeval
-- statement:
--   The Frobenius Group Field construction uses the sg aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SgAlgebraMap.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SgAlgebraMap.lean#L31-L39

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

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.sg_aeval (hv : v.Integers R) {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (j : ι) (hj : εT j ≠ 0)
    (a : O) (Q : ℤ_[p][X]) : sg j (aeval a Q) = aeval (sg j a) Q := by sorry
