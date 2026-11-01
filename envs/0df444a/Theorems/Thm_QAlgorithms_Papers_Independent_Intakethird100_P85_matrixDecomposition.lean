-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_matrixDecomposition
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.matrixDecomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:12:40.140371+00:00
-- url     : https://prove2.me/theorems/066a5830-9bb3-4440-89ba-026e059daf43
-- title:
--   Lemma 6 (Matrix decomposition): arbitrary finite dimension
-- statement:
--   Let $d\ge0$ and let $U$ be a unitary $d\times d$ complex matrix whose entries lie in $\mathbb D[\omega]$. There is a finite word of one- and two-level operations of types $X,H,T,\omega$, with product $W$, such that
--
--   $$U=W.$$
--
--   Two-level operations use distinct ordered coordinates. At $d=0$ the empty word gives the unique empty matrix. The result supplies the algebraic factorization used by exact circuit synthesis.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 4, Lemma 6 (Matrix decomposition): arbitrary finite dimension

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

/-- Lemma 6, PDF p.4: arbitrary finite-dimensional matrix factorization, including dimension 0. -/
theorem matrixDecomposition (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ)
    (unitary : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (ring : ∀ i j, InDomega (U i j)) :
    ∃ w : List (LevelOp d), levelWordMatrix w = U := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
