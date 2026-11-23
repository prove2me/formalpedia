-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_residue_uR
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix.residue_uR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:04.340124+00:00
-- url     : https://prove2.me/theorems/5bb031c9-3c41-4108-aca3-92449ff44f38
-- title:
--   Frobenius Valuation Matrix: residue u R
-- statement:
--   The Frobenius Valuation Matrix construction uses the residue u R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LiftMonomialDeterminantStatementHolds.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LiftMonomialDeterminantStatementHolds.lean#L44-L54

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

theorem ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix.residue_uR (hv : v.Integers R) [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    IsLocalRing.residue R (uR hv D j y) = lam (D.Λ.map (IsLocalRing.residue R)) j y := by sorry
