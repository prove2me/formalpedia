-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_tridiagonalHermitian
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.tridiagonalHermitian
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:21:10.927611+00:00
-- url     : https://prove2.me/theorems/14ace3d5-363b-4731-a8f5-f80e0684723c
-- title:
--   §3.3: Hermitian tridiagonal circuit (64)–(66)
-- statement:
--   Let $N=2^n$ and let nonzero-scale real data specify the symmetric tridiagonal matrix, with fixed zero sentinel at $2N-1$. On labels $(t,m)$ use the transpose involution (64), which fixes $m$ for even $t$ and flips it for odd $t$. Construct the row oracle as column composed with transpose, retain H3, and insert Z before the data rotation as in (66).
--
--   The resulting three-flag circuit satisfies
--   $$ U^\dagger=U,\qquad (\langle0|\otimes I)U(|0\rangle\otimes I)=A/(3M_a). $$
--   The permutations are chosen before the data values. This is the distinct Hermitian circuit (66), rather than a Hermiticity claim for the original (63).
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 17, §3.3: Hermitian tridiagonal circuit (64)–(66)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF pp.16-17, (64)-(66): a distinct transpose-based row oracle and Z
produce a Hermitian tridiagonal encoding without restoring the deletion flag. -/
theorem tridiagonalHermitian (n : ℕ) :
    ∃ B : Scheme n 2 (n + 1) 1, ∃ T : TransposeOracle B,
      TridiagonalLabels B ∧
      (∀ l, (T.transpose l).1 = l.1 ∧ (T.transpose l).2.val =
        if l.1.val % 2 = 0 then l.2.val else (l.2.val + 1) % 2) ∧
      Fintype.card (Bool × Fin 4) = 2 ^ 3 ∧
      ∀ a : Fin (2 * 2 ^ n - 1) → ℝ, 0 < tableMax (triTable n a) →
        B.matrix (triTable n a) = tridiagonal n a ∧
        QAlgorithms.IsBlockEncoding (false, 0) (B.simpleCircuit (triTable n a) true)
          (3 * tableMax (triTable n a)) 0 (tridiagonal n a) ∧
        (B.simpleCircuit (triTable n a) true)ᴴ = B.simpleCircuit (triTable n a) true := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
