-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_simplifiedConstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.simplifiedConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:08:07.584448+00:00
-- url     : https://prove2.me/theorems/509716ee-1dc1-42f5-af91-2261e0ae5d55
-- title:
--   §2.1.1: simplified base block encoding (11)–(12)
-- statement:
--   Let $N,D,M,S$ be powers of two with $DM=NS$. Fix reversible labels enumerating the structural entries bijectively, with no invalid labels and equal full row and column sparsities $S$. For any real supplied data table with $M_a=\max_j|a_j|>0$, circuit (11) is an exact unitary block encoding:
--   $$ (\langle0|\otimes I)U(|0\rangle\otimes I)=\frac{A}{S M_a}. $$
--   It uses one table loading of $D$ items and $1+\log_2 S$ flag qubits. Exactness refers to ideal rotations; finite rotation synthesis is a separate approximation. This is the introductory unpadded form of the base construction.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 6, §2.1.1: simplified base block encoding (11)–(12)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF pp.5-6, (11)-(12): no padding or invalid labels, equal full sparsities. -/
theorem simplifiedConstruction (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (ha : 0 < tableMax a) (hv : ∀ l, B.valid l = true)
    (hc : B.columnSlots = Finset.univ) (hr : B.rowSlots = Finset.univ) :
    QAlgorithms.IsBlockEncoding (false, 0) (B.simpleCircuit a)
      ((2 ^ s : ℕ) * tableMax a) 0 (B.matrix a) ∧
    loadingCost (baseLoadingSchedule (2 ^ d)) = 2 ^ d ∧
    Fintype.card (Bool × Fin (2 ^ s)) = 2 ^ (s + 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
