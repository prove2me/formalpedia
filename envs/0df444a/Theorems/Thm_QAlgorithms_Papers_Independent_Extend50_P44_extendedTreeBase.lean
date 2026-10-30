-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_extendedTreeBase
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.extendedTreeBase
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:21:52.550062+00:00
-- url     : https://prove2.me/theorems/a5a4f1dc-5580-4ce3-a6d9-31c42bcdf7d1
-- title:
--   §3.4: Hermitian extended-binary-tree base construction (67)–(74)
-- statement:
--   Let $n\ge1$ and $N=2^n$. Give the extended binary tree the edge between each vertex $i>0$ and $\lfloor i/2\rfloor$, edge weight $a_2$, diagonal weight $a_0$ at vertex 0 and at vertices $i\ge N/2$, and diagonal weight $a_1$ elsewhere. Assume $M_a=\max_{t<3}|a_t|>0$.
--
--   There are data-independent reversible labels (69)-(74), with a full transpose completion, such that the Hermitian base circuit obeys
--   $$ U^\dagger=U,\qquad (\langle0|\otimes I)U(|0\rangle\otimes I)=A/(4M_a). $$
--   Three supplied values occupy four physical data states; four supported sparsity states occupy three bits, giving five flags. At $N=2$ the internal-node weight need not occur. No preamplification or PREP improvement is asserted here.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 18, §3.4: Hermitian extended-binary-tree base construction (67)–(74)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF pp.17-18, (67)-(74): Hermitian extended-tree base construction.
The three data items occupy a four-state register; four supported sparsity
states occupy three bits. At n=1 the low-bit register is empty. -/
theorem extendedTreeBase (n : ℕ) (hn : 1 ≤ n) :
    ∃ B : Scheme n 3 2 (n + 1), ∃ T : TransposeOracle B,
      TreeLabels B ∧
      (∀ l, (T.transpose l).2.val = if l.1.val = 2 then
        (l.2.val + 2 ^ n) % 2 ^ (n + 1) else l.2.val) ∧
      loadingCost (baseLoadingSchedule 3) = 3 ∧
      Fintype.card ((Bool × Bool) × Fin 8) = 2 ^ 5 ∧
      ∀ a : Fin 3 → ℝ, 0 < tableMax a →
        B.matrix (treeTable a) = extendedTree n a ∧
        QAlgorithms.IsBlockEncoding ((false, false), 0) (B.baseCircuit (treeTable a) true)
          (4 * tableMax a) 0 (extendedTree n a) ∧
        (B.baseCircuit (treeTable a) true)ᴴ = B.baseCircuit (treeTable a) true := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
