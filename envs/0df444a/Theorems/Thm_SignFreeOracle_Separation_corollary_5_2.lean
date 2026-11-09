-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_corollary_5_2
-- name    : SignFreeOracle.Separation.corollary_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:27.734978+00:00
-- url     : https://prove2.me/theorems/de25345a-cf8d-4bf1-869c-d2c8ac176cd7
-- title:
--   Corollary 5.2 (corrected: positive sampling budget and integral parameters)
-- statement:
--   Fix a sufficiently large admissible $n$ and a valid base graph. Given an arbitrary $p$-bit witness map, $0<\gamma\le1$, and a positive integer $t$, one family $D_w$ satisfies the permutation guarantee of Lemma 5.1 and, for every fixed $G\in\{G_n,F_n(U)\}$ and every algorithm $A$ with at most $q$ adjacency-list queries,
--   $$\left|\Pr[A^{O_{G,\pi}}(w_\pi)=1]-\Pr[A^{O_{G,\pi'}}(w_\pi)=1]\right|\le\frac{2(p+\log_2(1/\gamma))\,2nq}{t}+\gamma.$$
--   Both experiments use the same $D_w$ and witness $w_\pi$, with the three draws in Lemma 5.1. The factor $2n$ is preserved. The family is chosen before the graph algorithm, the seed and the query budget. This transports the permutation information bound to the actual sorted adjacency-list model.
--
--   Differences from the source:
--   - correction: t is any natural number in a denominator → t is a positive natural number; reason: t=0 makes the displayed quotient undefined
--   - correction: n is an arbitrary positive integer while sqrt(n), depths and bit counts are used as dimensions → all sufficiently large admissible integral n; reason: n=2,k=1 requires 3-sqrt(2) children and is undefined; admissibility includes the unbounded sequence n=4^s
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - generalization: the selected base graph B_n → every base graph satisfying the original connectedness, regularity, size and girth bounds; reason: the proofs use exactly these base properties and specialize to the selected B_n
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
--   - encoding: neighbour positions i in [d] → zero-based natural positions, returning the queried label beyond the neighbour list; reason: positions outside the source query range have a graph-independent self answer and can be simulated without an oracle query
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Corollary 5.2, p. 16 (PDF p. 16)

import Definitions.Def_SignFreeOracle_Separation_Family
import Definitions.Def_SignFreeOracle_Separation_Experiments

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity

theorem corollary_5_2 : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Admissible n →
    ∀ (NB : ℕ) (B : SimpleGraph (Fin NB)), BaseConditions n NB B →
    ∀ (p t : ℕ) (w : Equiv.Perm (Fin (2 ^ bits n)) → Bits p) (γ : ℝ),
      1 ≤ t → 0 < γ → γ ≤ 1 →
      ∃ D : Bits p → PMF (PartialLabel (2 ^ bits n)), PresamplingGood w γ t D ∧
        ∀ (U : Set (Fin (2 ^ bits n))) (G : SimpleGraph (Fin (2 ^ bits n))),
          G = yesGraph n NB B ∨ G = noGraph n NB B U →
        ∀ (q : ℕ) (A : RandomQuery (Fin (2 ^ bits n) × ℕ) (Fin (2 ^ bits n)) (Bits p)),
          A.budget q →
          |permMean (fun π => A.accept (anyGraphQuery G π) (w π)) -
            resampledMean w D (fun π input => A.accept (anyGraphQuery G π) input)| ≤
              2 * ((p : ℝ) + Real.logb 2 (1 / γ)) * (2 * n * q) / t + γ := by sorry

end SignFreeOracle.Separation
