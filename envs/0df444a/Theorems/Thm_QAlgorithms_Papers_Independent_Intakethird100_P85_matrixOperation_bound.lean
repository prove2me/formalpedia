-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_matrixOperation_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.matrixOperation_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:15:43.873369+00:00
-- url     : https://prove2.me/theorems/eed1413d-6cd9-44bf-929c-a55a2f8b0d94
-- title:
--   §7, unnumbered: matrix decomposition operation count
-- statement:
--   There is an absolute constant $C>0$ such that, for every unitary $d\times d$ matrix $U$ over $\mathbb D[\omega]$ whose least natural denominator exponent is $k\ge1$, the successive-column elimination trace returns a reduction word $W$ and its expanded inverse satisfying
--
--   $$WU=I,\qquad W^{-1}=U,\qquad
--   |W|\le C3^d k,\quad |\operatorname{invword}(W)|\le C3^d k.
--   $$
--
--   The inverse word uses only the same one-/two-level alphabet, expanding inverses of $T$ and $\omega$ into seven positive copies. Constants precede all matrix data. This bounds the factorization output of Lemma 6; it does not bound arithmetic time.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 7, §7, unnumbered: matrix decomposition operation count

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P85

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P85

open scoped Classical BigOperators

open QAlgorithms

open QAlgorithms.Papers.Independent.Gap48.P10
  (InZomega InDomega Residue bits residue residueMultiply Reducible)

open QAlgorithms.Papers.Independent.Support21.P13
  (synthesisRing integralRing coordinateValue HTLetter htWordMatrix EntriesInRing cliffordTLibrary)

local notation "omega" => QAlgorithms.gateT true true

local notation "sqrtTwo" => ((Real.sqrt 2 : ℝ) : ℂ)

/-- Section 7, PDF pp.6–7: output of column elimination is O(3^d k), uniformly in U,d,k. -/
theorem matrixOperation_bound :
    ∃ C : ℕ, 0 < C ∧ ∀ (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) (k : ℕ),
      U ∈ Matrix.unitaryGroup (Fin d) ℂ → (∀ i j, InDomega (U i j)) →
      LeastMatrixExponent U k → 0 < k →
      ∃ w : List (LevelOp d), MatrixTrace U k w ∧ levelWordMatrix w * U = 1 ∧
        levelWordMatrix (inverseWord w) = U ∧
        w.length ≤ C * 3 ^ d * k ∧ (inverseWord w).length ≤ C * 3 ^ d * k := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
