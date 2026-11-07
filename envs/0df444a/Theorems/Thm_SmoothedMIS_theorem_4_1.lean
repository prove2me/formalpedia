-- Prove2me | Theorems.Thm_SmoothedMIS_theorem_4_1
-- name    : SmoothedMIS.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:43.633409+00:00
-- url     : https://prove2.me/theorems/11b0f8ec-5ff2-4442-9bc5-33e2bb19fbf0
-- title:
--   Theorem 4.1 — after addition-only smoothing, an MIS in $O(\sqrt{\log n})$ LOCAL rounds w.h.p.
-- statement:
--   For every constant $c>0$ there is a constant $\beta\ge1$, depending only on $c$, such that for every identifier range $\kappa$ there are a randomized LOCAL algorithm, knowing only $n$, and constants $C,n_0$ with the following property for all $n\ge n_0$. The algorithm runs at most $C\sqrt{\ln n}$ rounds, and for every graph $G$ on $n$ vertices and every assignment of distinct identifiers in $\{0,\dots,n^\kappa-1\}$, when it is run on the smoothing $\mathcal G=G\cup R$ with $p=\beta\ln n/n$, the set it computes is an MIS of $\mathcal G$ with probability at least $1-n^{-c}$. The probability is over the random edges and the random bits of the algorithm.
--
--   The algorithm sees only $\mathcal G$: neither $G$, nor $p$, nor which edges are random. Theorem 4.14 is derived from this statement by a coupling (§4.3).
--
--   Differences from the source:
--   - reading: for every c there is β; for all large n; let G be any graph; there is a randomized LOCAL algorithm → ∀ c > 0, ∃ β ≥ 1, ∀ κ, ∃ algorithm A, ∃ C, ∃ n0, ∀ n ≥ n0, then ∀ G and ∀ identifiers; reason: the algorithm is given only the smoothed graph, n and the identifiers and does not depend on G (§4.1 builds one algorithm); β depends only on c; this is the stronger reading
--   - reading: computes an MIS in O(√log n) rounds with probability at least 1 − n^{−c} → a fixed round budget A.rounds n ≤ C√ln n, and the computed set is an MIS with probability ≥ 1 − n^{−c}; reason: the paper's algorithm runs a number of rounds depending only on n and β (p.29); this Monte Carlo reading is the stronger one
--   - reading: distinct identifiers of O(log n) bits → injective identifiers < n^κ, for every constant κ, with A, C, n0 depending on κ; reason: O(log n) bits means values below n^κ for a constant κ
--   - reading: the port-numbered LOCAL model with a private source of randomness (§1.5) → broadcast with multiset reception and a private fair-coin tape per node (LocalAlg, tapeLaw); reason: with unbounded messages carrying identifiers this simulates ports after one round, so the existence claim is at least as strong
--   - encoding: p = β ln n/n → min(1, β ln n/n); reason: the same for all n with β ln n ≤ n, in particular for all large n
--   - encoding: with probability at least 1 − n^{−c} over the random edges and the random bits → a measurable sub-event of the success event of probability ≥ 1 − n^{−c} under smoothing law ⊗ tape law; reason: the algorithm is an arbitrary function of the tapes, so the success event need not be measurable; when it is, the two agree
--   - encoding: 𝒢 = G ∪ R, every non-edge of G added independently with probability p → addSmooth G ω = G ⊔ {pairs with coin true}, coins on all pairs; reason: coins on edges of G change nothing, so the law is the same
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Theorem 4.1, p.17 (PDF p.19); proof §4.2.2, p.29

import Mathlib
import Definitions.Def_SmoothedMIS_IsMIS
import Definitions.Def_SmoothedMIS_LocalAlg
import Definitions.Def_SmoothedMIS_smoothLaw

open MeasureTheory

namespace SmoothedMIS

/-- **Theorem 4.1** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis for Distributed MIS*
(manuscript, sha256 dc2131db…), Theorem 4.1, p.17). For every constant `c > 0`, there is a constant `β ≥ 1`, depending only on `c`, such that
the following holds for all sufficiently large `n`. Let `G` be any graph on `n` vertices, and let
`𝒢` be its smoothing with `λ = β ln n`. There is a randomized LOCAL algorithm that, given `𝒢`, the
number `n`, and distinct identifiers of `O(log n)` bits, computes an MIS of `𝒢` in `O(√log n)`
rounds with probability at least `1 − n^{−c}`. The probability is over the random edges and the
random bits of the algorithm.

**Formalization Note**
* `𝒢 = G ∪ R` is `addSmooth G ω` (every pair with coin `true` is added), with coins of probability `min 1 (β ln n/n)` (`smoothLaw n β`); vertices are `Fin n`.
* The algorithm is a `LocalAlg ℕ Unit Bool` that knows only `n` (and, being chosen after `κ`,
  the identifier range); it runs on the smoothed graph, does not see `G`, `p` or which edges are
  random, and outputs the set of nodes answering `true`.
* Quantifier order: `∀ c > 0, ∃ β ≥ 1, ∀ κ, ∃ A, ∃ C, ∃ n0, ∀ n ≥ n0`, then the round budget
  `A.rounds n ≤ C √(ln n)` (fixed in advance, a function of `n` only) and, for every base graph
  `G` and every injective identifier assignment with values `< n^κ` ("`O(log n)` bits"), an MIS of
  the smoothed graph with probability `≥ 1 − n^{−c}` over the edge coins and the nodes' private
  fair-coin tapes jointly (`smoothLaw n β ⊗ tapeLaw (Fin n)`).
* The success event need not be measurable; the statement asserts a measurable subevent of
  probability `≥ 1 − n^{−c}`. -/
theorem theorem_4_1 :
    ∀ c : ℝ, 0 < c → ∃ β : ℝ, 1 ≤ β ∧ ∀ κ : ℕ, ∃ A : LocalAlg ℕ Unit Bool, ∃ C : ℝ, ∃ n0 : ℕ,
      ∀ n ≥ n0, (A.rounds n : ℝ) ≤ C * Real.sqrt (Real.log n) ∧
        ∀ (G : SimpleGraph (Fin n)) (ids : Fin n → ℕ), Function.Injective ids →
          (∀ v, ids v < n ^ κ) →
          ∃ E : Set ((Sym2 (Fin n) → Bool) × (Fin n → ℕ → Bool)), MeasurableSet E ∧
            E ⊆ {ω | IsMIS (addSmooth G ω.1) (A.outSet (addSmooth G ω.1) n ids ω.2)} ∧
            1 - (n : ℝ) ^ (-c) ≤ (((smoothLaw n β).prod (tapeLaw (Fin n))) E).toReal := by sorry

end SmoothedMIS
