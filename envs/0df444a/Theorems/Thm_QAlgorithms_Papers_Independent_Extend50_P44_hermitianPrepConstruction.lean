-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_hermitianPrepConstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.hermitianPrepConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:14:56.037596+00:00
-- url     : https://prove2.me/theorems/65a012c0-c930-4684-b09c-268706afe4c7
-- title:
--   §2.4: Hermitian PREP/UNPREP construction (38)
-- statement:
--   Use the symmetric commuting-data layout of (31), with an involutive transpose oracle preserving the data and range predicates. Let $p=1/2$, with nonzero active real data and zero padding. Write $F$ for the full initial preparation on the physical sparsity register: PREP on the column data factor together with its residual preparation. Write $G$ for the full final unpreparation: UNPREP on the row data factor together with the adjoint residual preparation. Require the full operator identity (38), including the actual residual-register embeddings:
--   $$ F=S_c G^*, $$
--   where $S_c$ is the sign oracle on the column data factor, tensored with residual identity, and $*$ means adjoint. The sign oracle uses +1 on zero slots. Then circuit (31) is unitary and Hermitian, and its selected block is $A/α_{1/2}$ with the normalization (32). It has two preparation loads and $s+1$ flags. Matching only the data-register matrices, their prepared states, or the residual diagonal blocks does not imply this full-unitary conclusion.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 12, §2.4: Hermitian PREP/UNPREP construction (38)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF p.12, (38): matching full physical preparation operators at p=1/2
give Hermiticity of the entire circuit, retaining PREP resources. The identity
includes the residual-register preparations and their actual tensor embeddings;
matching only the data matrices or the residual diagonal blocks is insufficient. -/
theorem hermitianPrepConstruction (B : Scheme n s d m) (T : TransposeOracle B)
    (L : PrepLayout B) (a : Fin (2 ^ d) → ℝ)
    (hnz : ∀ j ∈ L.active, a j ≠ 0)
    (hzero : ∀ j, j ∉ L.active → a j = 0)
    (P : PreparationPair L a (1 / 2))
    (hmatching : tensorPreparation L.factorColumn P.prep L.Hcolumn =
      tensorPreparation L.factorColumn (signOracle a)
        (1 : Matrix (Fin (2 ^ L.kc)) (Fin (2 ^ L.kc)) ℂ) *
      (tensorPreparation L.factorRow P.unprep L.Hrowᴴ)ᴴ) :
    QAlgorithms.IsBlockEncoding (false, 0) (L.circuit P) (L.alpha a (1 / 2)) 0 (B.matrix a) ∧
    (L.circuit P)ᴴ = L.circuit P ∧
    loadingCost (doubleLoadingSchedule L.active.card) = 2 * L.active.card ∧
    Fintype.card (Bool × Fin (2 ^ s)) = 2 ^ (s + 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
