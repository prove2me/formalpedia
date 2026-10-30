-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_checkerboardCornerDeletion
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.checkerboardCornerDeletion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:17:04.349374+00:00
-- url     : https://prove2.me/theorems/38ad8b5b-775e-42de-be97-be2c11dc9156
-- title:
--   §3.1: corner-deleted checkerboard adaptation (49)
-- statement:
--   Let $n\ge1$, $N=2^n$, and let $A$ be the checkerboard matrix with entries $a_{(i+j)\bmod2}$, where the real values are not both zero. Replace only entries $(0,0)$ and $(N-1,N-1)$ by zero, obtaining $A'$. Keep the row and column permutations (41)-(42), and use (49) to delete labels $(0,0)$ and $(0,N^2/2-1)$.
--
--   The resulting base and PREP circuits exactly block encode $A'$ with, respectively,
--   $$ \alpha_{\rm base}=N\max(|a_0|,|a_1|),\qquad \alpha_{\rm PREP}=N(|a_0|+|a_1|)/2. $$
--   Only the range predicate changes. This gives an explicit example of structural-zero deletion without loading a new data value.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 14, §3.1: corner-deleted checkerboard adaptation (49)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF pp.13-14, (49): the same checkerboard label permutations with a
range oracle deleting the two corner labels work in both constructions. -/
theorem checkerboardCornerDeletion (n : ℕ) (hn : 1 ≤ n) :
    ∃ B : Scheme n n 1 (2 * n - 1), ∃ L : PrepLayout (deleteCheckerCorners B),
      CheckerLabels B ∧ L.active = Finset.univ ∧
      ∀ a : Fin 2 → ℝ, 0 < tableMax a →
      ∃ P : PreparationPair L a (1 / 2),
        (deleteCheckerCorners B).matrix a = deletedCheckerboard n a ∧
        QAlgorithms.IsBlockEncoding ((false, false), 0)
          ((deleteCheckerCorners B).baseCircuit a)
          ((2 ^ n : ℕ) * max |a 0| |a 1|) 0 (deletedCheckerboard n a) ∧
        QAlgorithms.IsBlockEncoding (false, 0) (L.circuit P)
          ((2 ^ n : ℕ) * (|a 0| + |a 1|) / 2) 0 (deletedCheckerboard n a) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
