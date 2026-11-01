-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_columnReduction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.columnReduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:12:09.891108+00:00
-- url     : https://prove2.me/theorems/e7d86d42-bdfa-4e15-8dfe-01fad114b185
-- title:
--   Lemma 5 (Column lemma): reduce a unit column to e1
-- statement:
--   Let $d>0$ and let $u\in\mathbb D[\omega]^d$ be a unit vector, so $\sum_j|u_j|^2=1$. Then a finite sequence of one- and two-level operations of types $X,H,T,\omega$ has product $W$ satisfying
--
--   $$Wu=e_1.$$
--
--   Two-level operations act on distinct ordered coordinates and are the identity elsewhere; a one-level $\omega$ multiplies one coordinate by $\omega$. The equality retains absolute phase. This reduces an arbitrary-dimensional unit column to the first standard basis vector.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 4, Lemma 5 (Column lemma): reduce a unit column to e1

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

/-- Lemma 5, PDF p.4: arbitrary positive-dimensional unit columns reduce exactly to e1. -/
theorem columnReduction (d : ℕ) (positive : 0 < d) (u : Fin d → ℂ)
    (ring : ∀ i, InDomega (u i)) (normalized : vectorNormSq u = 1) :
    ∃ w : List (LevelOp d), (levelWordMatrix w).mulVec u =
      (fun i => if i = (⟨0, positive⟩ : Fin d) then 1 else 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
