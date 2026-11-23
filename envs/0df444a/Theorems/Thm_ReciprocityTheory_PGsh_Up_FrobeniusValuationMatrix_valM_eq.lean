-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_valM_eq
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix.valM_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:58.266699+00:00
-- url     : https://prove2.me/theorems/6e4dcc44-888f-436f-bb38-c003f090195e
-- title:
--   Frobenius Valuation Matrix: val M eq
-- statement:
--   The Frobenius Valuation Matrix construction uses the val M eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LiftMonomialDeterminantStatementHolds.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LiftMonomialDeterminantStatementHolds.lean#L79-L85

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

theorem ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix.valM_eq (hv : v.Integers R) (D : Lifts H U X) :
    valM D = (MuR hv D).map (algebraMap R C) *
      Matrix.diagonal fun α : Nb p g => algebraMap R C (∏ j, D.ε j ^ (α j).val) := by sorry
