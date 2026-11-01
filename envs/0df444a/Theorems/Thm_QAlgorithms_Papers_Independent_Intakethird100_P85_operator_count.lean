-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_operator_count
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.operator_count
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:16:52.302506+00:00
-- url     : https://prove2.me/theorems/59b83ed5-e8d5-4692-8644-b3c6bc63c2d5
-- title:
--   §8, unnumbered: number of bounded-denominator operators
-- statement:
--   For $n\ge1$ and $k\ge0$, let $\mathcal U_{n,k}$ be the set of distinct unitary $n$-qubit matrices for which $k$ is a denominator exponent, meaning $(\sqrt2)^kU$ has entries in $\mathbb Z[\omega]$. The set is finite and
--
--   $$2^{2^{n-1}k}\le |\mathcal U_{n,k}|\le 2^{4^n(4+2k)}.$$
--
--   Matrices are counted with absolute phase retained. The exponent $k$ need not be least, so these are nested sets as $k$ increases. Taking logarithms yields the source's information-size interpretation for positive $k$. This is a count of operators, not a lower bound on the complexity of every individual operator.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 7, §8, unnumbered: number of bounded-denominator operators

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

/-- Section 8, PDF p.7: finite number of distinct operators with a valid denominator k. -/
theorem operator_count (n k : ℕ) (positive : 1 ≤ n) :
    Finite (boundedOperators n k) ∧
    2 ^ (2 ^ (n - 1) * k) ≤ Nat.card (boundedOperators n k) ∧
    Nat.card (boundedOperators n k) ≤ 2 ^ (4 ^ n * (4 + 2 * k)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
