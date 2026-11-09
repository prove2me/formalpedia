-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_proposition_5_3
-- name    : SignFreeOracle.Separation.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:09.314966+00:00
-- url     : https://prove2.me/theorems/eca6810a-655e-4bb6-b9c0-c98628470374
-- title:
--   Proposition 5.3 (corrected: integral construction parameters) — no polynomial MA protocol
-- statement:
--   Fix polynomial witness and query bounds $p,q$. For every sufficiently large admissible $n$, for every valid base graph, every randomized adaptive verifier using $p(m(n))$ witness bits and at most $q(m(n))$ graph queries fails on some labelled graph in
--   $$\{G_n\}\cup\{F_n(U):|U|\le2^{\sqrt n}\}.$$
--   Explicitly, either a YES labelling accepts every witness with probability strictly below $2/3$, or some NO labelling and witness accept with probability strictly above $1/3$. The size threshold is chosen after the resource polynomials and before size, base graph, algorithm, labels, seeds and witnesses. This states a per-size lower bound, including every MA protocol; the finite query-tree version also permits nonuniform local computation at each size. It does not assert a different oracle for each input as the main goal.
--
--   Differences from the source:
--   - correction: n is an arbitrary positive integer while sqrt(n), depths and bit counts are used as dimensions → all sufficiently large admissible integral n; reason: n=2,k=1 requires 3-sqrt(2) children and is undefined; admissibility includes the unbounded sequence n=4^s
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - generalization: the selected base graph B_n → every base graph satisfying the original connectedness, regularity, size and girth bounds; reason: the proofs use exactly these base properties and specialize to the selected B_n
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
--   - generalization: polynomially bounded MA protocols → all finite randomized query trees at each size with fixed polynomial resource bounds; reason: the proof's threshold depends only on p and q, and this includes every uniform finite-machine MA protocol
--   - encoding: neighbour positions i in [d] → zero-based natural positions, returning the queried label beyond the neighbour list; reason: positions outside the source query range have a graph-independent self answer and can be simulated without an oracle query
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Proposition 5.3, p. 16 (PDF p. 16)

import Definitions.Def_SignFreeOracle_Separation_Family
import Definitions.Def_SignFreeOracle_Separation_Experiments

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity

/-- Uniform polynomial bounds precede n and all algorithms, labels, seeds and witnesses.
Allowing an arbitrary finite query tree at each size strengthens the protocol lower bound. -/
theorem proposition_5_3 (p q : Polynomial ℕ) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Admissible n →
    ∀ (NB : ℕ) (B : SimpleGraph (Fin NB)), BaseConditions n NB B →
    ∀ A : RandomQuery (Fin (2 ^ bits n) × ℕ) (Fin (2 ^ bits n)) (Bits (p.eval (bits n))),
      A.budget (q.eval (bits n)) →
      (∃ π : Equiv.Perm (Fin (2 ^ bits n)), ∀ w,
        A.accept (anyGraphQuery (yesGraph n NB B) π) w < (2 / 3 : ℝ)) ∨
      (∃ (U : Set (Fin (2 ^ bits n))) (π : Equiv.Perm (Fin (2 ^ bits n)))
          (w : Bits (p.eval (bits n))), U.ncard ≤ 2 ^ Nat.sqrt n ∧
        (1 / 3 : ℝ) < A.accept (anyGraphQuery (noGraph n NB B U) π) w) := by sorry

end SignFreeOracle.Separation
