-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_baseConstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.baseConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:07:10.512229+00:00
-- url     : https://prove2.me/theorems/b2d33a7f-8fc0-44ff-af31-06ccf1066caf
-- title:
--   Abstract main construction, pinned to §2.1.2, circuit (16) and (17)
-- statement:
--   Let $N=2^n$, let $2^s$ be the physical sparsity-register dimension, and let $2^d2^m=N2^s$. Fix reversible row and column label maps, a range predicate enumerating each structural matrix position once, and unitary preparations uniform on $S_c$ and $S_r$ supported sparsity states. These choices precede the real data values $a_j$. Let $D$ count the supplied table slots; padded data values are fixed to zero, and $M_a=\max_j|a_j|>0$.
--
--   The circuit (16), consisting of column uncomputation, one multiplexed RX data loader, range deletion and row computation between the two preparations, is unitary and satisfies
--   $$ (\langle0|\otimes I)U(|0\rangle\otimes I)=\frac{A}{\sqrt{S_cS_r}\,M_a}. $$
--   It loads $D$ data items and has $s+2$ flag qubits. Arithmetic efficiency is conditional on the supplied oracle implementations. This construction separates the matrix pattern from its numerical values.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 7, Abstract main construction, pinned to §2.1.2, circuit (16) and (17)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF pp.1,6-7, (16)-(17): full base construction for padded arithmetic labels.
No claim of efficient arithmetic is made without its implementation hypothesis. -/
theorem baseConstruction (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (active : Finset (Fin (2 ^ d))) (hactive : active.Nonempty)
    (hpadding : ∀ j, j ∉ active → a j = 0)
    (ha : 0 < tableMax a) :
    QAlgorithms.IsBlockEncoding ((false, false), 0) (B.baseCircuit a)
      (B.baseAlpha a) 0 (B.matrix a) ∧
    loadingCost (baseLoadingSchedule active.card) = active.card ∧
    Fintype.card ((Bool × Bool) × Fin (2 ^ s)) = 2 ^ (s + 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
