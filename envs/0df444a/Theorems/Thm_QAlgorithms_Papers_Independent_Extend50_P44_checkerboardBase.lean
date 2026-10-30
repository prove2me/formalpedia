-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_checkerboardBase
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.checkerboardBase
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:15:41.34728+00:00
-- url     : https://prove2.me/theorems/2da55c7c-10dd-47cf-bff6-5cbce34c3492
-- title:
--   §3.1: checkerboard base circuit and costs (40)–(44)
-- statement:
--   Let $n\ge1$ and $N=2^n$. There are fixed arithmetic label oracles (41)-(42), chosen independently of the two real values $a_0,a_1$, for the checkerboard matrix $A_{ij}=a_{(i+j)\bmod2}$. For every table with $\max(|a_0|,|a_1|)>0$, the no-deletion base circuit satisfies
--   $$ (\langle0|\otimes I)U(|0\rangle\otimes I)=\frac{A}{N\max(|a_0|,|a_1|)}. $$
--   It loads two items, uses $n+1$ flags, and its arithmetic oracles use only X and CNOT gates, hence zero Toffoli/T cost. No full-unitary Hermiticity is asserted for (43). This example demonstrates repeated-value loading with data-independent structure.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 13, §3.1: checkerboard base circuit and costs (40)–(44)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF p.13, (43)-(44): checkerboard construction, with exactly two loaded
data slots, n+1 flags, and zero Toffoli cost in the arithmetic oracles. -/
theorem checkerboardBase (n : ℕ) (hn : 1 ≤ n) :
    ∃ B : Scheme n n 1 (2 * n - 1), CheckerLabels B ∧ B.ArithmeticCost 0 0 ∧
      loadingCost (baseLoadingSchedule 2) = 2 ∧
      Fintype.card (Bool × Fin (2 ^ n)) = 2 ^ (n + 1) ∧
      ∀ a : Fin 2 → ℝ, 0 < tableMax a →
        B.matrix a = checkerboard n a ∧
        QAlgorithms.IsBlockEncoding (false, 0) (B.simpleCircuit a)
          ((2 ^ n : ℕ) * max |a 0| |a 1|) 0 (checkerboard n a) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
