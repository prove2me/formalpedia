-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_columnOperation_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.columnOperation_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:14:56.823205+00:00
-- url     : https://prove2.me/theorems/8fd4c712-8181-437e-9d05-a6c76fa46add
-- title:
--   §7, unnumbered: column reduction operation count
-- statement:
--   Count each one-/two-level $X,H,T,\omega$ as one operation. There is an absolute constant $C>0$ with all the following properties. For every pair satisfying Lemma 4 at a valid exponent $k>0$, the selected row word lowers the exponent and has at most $C$ letters. For every unit column $u\in\mathbb D[\omega]^d$, $d>0$, at a valid exponent $k>0$, there are a single-pass word $P$ and a complete-reduction word $W$, recorded by the column proof's traces, such that
--
--   $$
--   (\sqrt2)^{k-1}Pu\in\mathbb Z[\omega]^d,\quad |P|\le Cd,
--   \qquad Wu=e_1,\quad |W|\le Cdk.
--   $$
--
--   The same constant works for all dimensions, exponents and input columns. Word lengths are actual output counts; the statement makes no arithmetic runtime claim. It quantifies the size of the column reduction used in synthesis.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 6, §7, unnumbered: column reduction operation count

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

/-- Section 7, PDF p.6: uniform row, one-pass, and complete-column output bounds.
The positive-exponent domain excludes the nontrivial exponent-zero base-case cost. -/
theorem columnOperation_bound :
    ∃ C : ℕ, 0 < C ∧
    (∀ (u : Bool → ℂ) (k : ℕ), (∀ b, InDomega (u b)) → 0 < k →
      VectorExponent u k →
      residueNorm (kResidue (u false) k) = residueNorm (kResidue (u true) k) →
      VectorExponent ((htWordMatrix (rowWord u k)).mulVec u) (k - 1) ∧
        (rowWord u k).length ≤ C) ∧
    (∀ (d : ℕ) (u : Fin d → ℂ) (k : ℕ), 0 < d → 0 < k →
      (∀ i, InDomega (u i)) → vectorNormSq u = 1 → VectorExponent u k →
      ∃ w : List (LevelOp d), PassTrace k u w ∧
        VectorExponent ((levelWordMatrix w).mulVec u) (k - 1) ∧ w.length ≤ C * d) ∧
    (∀ (d : ℕ) (hd : 0 < d) (u : Fin d → ℂ) (k : ℕ), 0 < k →
      (∀ i, InDomega (u i)) → vectorNormSq u = 1 → VectorExponent u k →
      ∃ w : List (LevelOp d), ColumnTrace ⟨0, hd⟩ u k w ∧
        (levelWordMatrix w).mulVec u = (fun i => if i = (⟨0, hd⟩ : Fin d) then 1 else 0) ∧
        w.length ≤ C * d * k) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
