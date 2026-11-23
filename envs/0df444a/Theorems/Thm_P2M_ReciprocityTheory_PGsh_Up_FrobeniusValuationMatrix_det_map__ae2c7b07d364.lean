-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_det_map__ae2c7b07d364
-- name    : P2M_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_det_map__ae2c7b07d364
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:11.203149+00:00
-- url     : https://prove2.me/theorems/c5affc86-854c-4c77-ae5d-2b1111235a46
-- title:
--   P2 M Reciprocity Theory PGsh Up Frobenius Valuation Matrix det map  ae2c7b07d364: P2 M Reciprocity Theory PGsh Up Frobenius Valuation Matrix det map  ae2c7b07d364
-- statement:
--   The P2 M Reciprocity Theory PGsh Up Frobenius Valuation Matrix det map  ae2c7b07d364 construction uses the P2 M Reciprocity Theory PGsh Up Frobenius Valuation Matrix det map  ae2c7b07d364 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LiftMonomialDeterminantStatementHolds.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LiftMonomialDeterminantStatementHolds.lean#L28-L30

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

theorem P2M_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_det_map__ae2c7b07d364 {S : Type} [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) : (M.map f).det = f M.det := by sorry

alias «ReciprocityTheory».«PGsh».«Up».«FrobeniusValuationMatrix».«det_map'» := P2M_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_det_map__ae2c7b07d364
