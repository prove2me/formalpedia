-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_sg_algebraMap
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.sg_algebraMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:56.432675+00:00
-- url     : https://prove2.me/theorems/1c9235e0-87ff-48bc-bc2a-7007d5a0e91e
-- title:
--   Frobenius Group Field: sg algebra Map
-- statement:
--   The Frobenius Group Field construction uses the sg algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SgAlgebraMap.lean#L12-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SgAlgebraMap.lean#L12-L29

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

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.sg_algebraMap (hv : v.Integers R) {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (j : ι) (hj : εT j ≠ 0)
    (z : ℤ_[p]) : sg j (algebraMap ℤ_[p] O z) = algebraMap ℤ_[p] R z := by sorry
