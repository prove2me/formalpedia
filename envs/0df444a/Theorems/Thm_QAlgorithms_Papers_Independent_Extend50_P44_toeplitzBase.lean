-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_toeplitzBase
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.toeplitzBase
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:17:47.652787+00:00
-- url     : https://prove2.me/theorems/2e0f75be-c771-43f6-b12b-1c8179c08712
-- title:
--   §3.2: banded Toeplitz block encoding (50)–(55)
-- statement:
--   For $N=2^n$, $D=2^d\le N$ and $0\le k<D$, fix the Toeplitz labels (51) and the overflow test (52), independently of the real values $a_t$. Let $A_{ij}=a_t$ when $i-j=t-k$ for $0\le t<D$, and zero otherwise. If $M_a=\max_t|a_t|>0$, the base circuit has
--   $$ (\langle0|\otimes I)U(|0\rangle\otimes I)=A/(D M_a). $$
--   It loads $D$ items and uses $d+2$ flags. One absolute constant bounds the arithmetic Toffoli count by $C(n+1)$, uniformly over $n,d,k$ and the values, with clean work returned to zero. The signed integer offset is range-tested rather than wrapped into the target matrix.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 15, §3.2: banded Toeplitz block encoding (50)–(55)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF pp.14-15, (50)-(55): banded Toeplitz encoding. The absolute constant
precedes the dimensions, offset and data. The arithmetic is O(log N), including
a harmless small-size constant; the overflow qubit is a flag. -/
theorem toeplitzBase :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ), d ≤ n → ∀ k : Fin (2 ^ d),
      ∃ B : Scheme n d d n, ToeplitzLabels B k ∧
        (∃ work, B.ArithmeticCost (C * (n + 1)) work) ∧
        loadingCost (baseLoadingSchedule (2 ^ d)) = 2 ^ d ∧
        Fintype.card ((Bool × Bool) × Fin (2 ^ d)) = 2 ^ (d + 2) ∧
        ∀ a : Fin (2 ^ d) → ℝ, 0 < tableMax a →
          B.matrix a = bandedToeplitz n d k a ∧
          QAlgorithms.IsBlockEncoding ((false, false), 0) (B.baseCircuit a)
            ((2 ^ d : ℕ) * tableMax a) 0 (bandedToeplitz n d k a) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
