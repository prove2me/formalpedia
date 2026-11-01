-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_recursive_t_count_growth
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.recursive_t_count_growth
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:12:30.855304+00:00
-- url     : https://prove2.me/theorems/918ea333-7489-48f6-a4b1-3a83cce0bd38
-- title:
--   Unnumbered §V: worst-case recursive T-count growth
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   Supply a depth-$n$ recursion tree using the five-factor composition $VWV^\dagger W^\dagger U$ at every internal node, with all three child subtrees at the previous depth. Suppose every leaf is a canonical presentation of T-count at most $t\in\mathbb N$. Then the exact recursively composed gate has both a Clifford/T presentation and a canonical presentation satisfying
--
--   $$\operatorname{cost}_T\le t\,5^n.$$
--
--   This explicit bound implies the advertised worst-case $O(t5^n)$ growth. Auxiliary recursive choices are supplied as data; this statement concerns T-cost growth and supplies no additional approximation-accuracy claim.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 5, Unnumbered §V: worst-case recursive T-count growth

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Unnumbered §V, PDF p.5, five-factor recurrence Eq.(1).
The explicit uniform upper bound implies the advertised O(t*5^n).
Inverses have available charged cost equal to that of their input, and
canonical reduction cannot increase the minimum exact charged cost. -/
theorem recursive_t_count_growth (t n : ℕ) (tree : RecursionTree n)
    (hbase : LeavesBounded t tree) :
    (∃ w : List CTLetter,
      SameGate (ctValue w) (recursionValue tree) ∧ chargedT w ≤ t * 5 ^ n) ∧
    (∃ c : CanonicalOutput,
      BsCanonical c.body ∧ SameGate (canonicalValue c) (recursionValue tree) ∧
        bsTCount c.body ≤ t * 5 ^ n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
