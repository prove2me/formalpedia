-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_tridiagonalBase
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.tridiagonalBase
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:19:33.466237+00:00
-- url     : https://prove2.me/theorems/d33a68de-158b-4fe4-a1ae-0adabb842fd0
-- title:
--   §3.3: symmetric tridiagonal encoding (57)–(62)
-- statement:
--   For $N=2^n$, let real values $a_0,\ldots,a_{2N-2}$ specify the symmetric tridiagonal matrix with diagonal $a_{2i}$ and adjacent entries $a_{2i+1}$. Append a fixed zero sentinel at address $2N-1$ and assume the resulting maximum magnitude $M_a$ is positive. A label scheme (58)-(60), chosen before the data, and the H3 preparation on 00,01,11 give
--   $$ (\langle0|\otimes I)U(|0\rangle\otimes I)=A/(3M_a). $$
--   The base circuit has four flags and $2N$ padded loading slots. An absolute constant bounds arithmetic Toffoli count by $C(n+1)$ with no extra work qubits. The sparse-access reference flag register has $n+3$ bits. The construction includes $N=1$ and $N=2$ using the same effective sparsity support.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 16, §3.3: symmetric tridiagonal encoding (57)–(62)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF pp.15-16, (57)-(62): symmetric tridiagonal base construction.
Three supported sparsity states give normalization 3 max|a| despite four
physical states. Arithmetic needs no extra work qubits; data uses 2N slots. -/
theorem tridiagonalBase :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ B : Scheme n 2 (n + 1) 1,
      TridiagonalLabels B ∧ B.ArithmeticCost (C * (n + 1)) 0 ∧
      loadingCost (baseLoadingSchedule (2 * 2 ^ n)) = 2 * 2 ^ n ∧
      Fintype.card ((Bool × Bool) × Fin 4) = 2 ^ 4 ∧
      Fintype.card ((Bool × Bool × Bool) × Fin (2 ^ n)) = 2 ^ (n + 3) ∧
      ∀ a : Fin (2 * 2 ^ n - 1) → ℝ, 0 < tableMax (triTable n a) →
        B.matrix (triTable n a) = tridiagonal n a ∧
        QAlgorithms.IsBlockEncoding ((false, false), 0) (B.baseCircuit (triTable n a))
          (3 * tableMax (triTable n a)) 0 (tridiagonal n a) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
