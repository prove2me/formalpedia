-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_tridiagonalNoDeletion
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.tridiagonalNoDeletion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:20:23.786687+00:00
-- url     : https://prove2.me/theorems/25926c18-8880-43ef-b1df-d56d26ca6944
-- title:
--   §3.3: tridiagonal circuit with no deletion flag (63)
-- statement:
--   Let $N=2^n$ and let $A$ be the symmetric tridiagonal matrix specified by real diagonal/interleaved adjacent values. Define its padded table by setting the last slot $a_{2N-1}=0$, and assume $M_a>0$. There are fixed label permutations for which circuit (63), containing H3 on the three supported states and the data loader but no range oracle or deletion flag, satisfies
--   $$ (\langle0|\otimes I)U(|0\rangle\otimes I)=A/(3M_a). $$
--   It has three physical flags and $2N$ padded loading slots. The zero sentinel is constructed from the input table, not supplied by a separate hypothesis about an unrelated value. This removes the range-deletion qubit from the preceding construction.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 16, §3.3: tridiagonal circuit with no deletion flag (63)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF p.16, (63): the fixed zero sentinel removes range deletion entirely.
H3 remains supported on 00,01,11 and only three flag qubits remain. -/
theorem tridiagonalNoDeletion (n : ℕ) :
    ∃ B : Scheme n 2 (n + 1) 1, TridiagonalLabels B ∧
      loadingCost (baseLoadingSchedule (2 * 2 ^ n)) = 2 * 2 ^ n ∧
      Fintype.card (Bool × Fin 4) = 2 ^ 3 ∧
      ∀ a : Fin (2 * 2 ^ n - 1) → ℝ, 0 < tableMax (triTable n a) →
        B.matrix (triTable n a) = tridiagonal n a ∧
        QAlgorithms.IsBlockEncoding (false, 0) (B.simpleCircuit (triTable n a))
          (3 * tableMax (triTable n a)) 0 (tridiagonal n a) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
