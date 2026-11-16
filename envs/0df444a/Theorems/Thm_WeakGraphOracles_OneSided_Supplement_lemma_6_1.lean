-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_Supplement_lemma_6_1
-- name    : WeakGraphOracles.OneSided.Supplement.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:30:51.244736+00:00
-- url     : https://prove2.me/theorems/349d1706-c9cc-4889-8d86-01ead8db2e9a
-- title:
--   Lemma 6.1 (informal Theorem 5) — $P_d^+$: two-sided GEN1 tester with $\tilde O(d^2/\epsilon^2)$ queries; one-sided testers need $n/8$ even in GEN2
-- statement:
--   Let $d\ge1$ be an integer and let $P_d^+$ be the property that at least $n/2$ of the $n$ vertices have degree at least $d$. Farness is measured by $\mathrm{dist}_\oplus$.
--
--   1. There is a universal constant $C>0$ such that for every $d\ge1$ and every $\epsilon\in(0,1]$ there is a query bound
--   $$q\ \le\ C\,\frac{d^2\,(1+\ln(1/\epsilon))}{\epsilon^2},$$
--   independent of $n$, and for every $n$ a GEN1 policy making at most $q$ queries that accepts every graph in $P_d^+$ and rejects every graph $\epsilon$-far from $P_d^+$, each with probability at least $2/3$.
--   2. For every $d\ge1$ and every $0<\epsilon<1/3$ there is $N$ such that for every $n\ge N$, every one-sided error $\epsilon$-tester for $P_d^+$ on $n$-vertex graphs, even in GEN2 (with degree queries), makes at least $n/8$ queries.
--
--   This is the paper's separation of one-sided and two-sided error for a natural non-monotone property in GEN1 (informal Theorem 5).
--
--   Differences from the source:
--   - generalization: Õ(d²/ε²) queries → q ≤ C·d²·(1 + ln(1/ε))/ε² with a universal C > 0; reason: the proof (§7.7) gives O(d² ln(1/ε)/ε²), a specific Õ(d²/ε²) bound with no log d factor, so the Lean bound implies the printed one; 1 + ln(1/ε) keeps the bound nonzero at ε = 1
--   - encoding: for every ε < 1/3 and large enough n; an ε-tester has ε > 0 (Definition 1) → ∀ d ≥ 1, ∀ 0 < ε < 1/3, ∃ N, ∀ n ≥ N; reason: the threshold may depend on the fixed d and ε, as in the source; positivity is the standing tester domain of Definition 1
--   - encoding: even in GEN2 → every randomized policy over the GEN2 alphabet (GEN1 queries and exact degree queries); reason: the GEN2 model of §3
--   - encoding: G is ε-far from P: its dist⊕ distance to the closest graph of P is at least ε → ε ≤ dist⊕(G, G') for every G' ∈ P on the same labels; reason: same condition (finitely many graphs, the minimum is attained); an empty P makes every graph far, the +∞ convention
--   - encoding: testable: a tester with query complexity independent of n → ∀ ε > 0, ∃ q, ∀ n, ∃ one policy of depth ≤ q correct on every n-vertex graph; reason: Definition 1 and Remark 2: a non-uniform family of testers, one per n, with ε wired in
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 12 (PDF p. 13), Lemma 6.1; informal version p. 3 (PDF p. 4), Theorem 5; proof §7.7, pp. 21–23 (PDF pp. 22–24)

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_models
import Definitions.Def_WeakGraphOracles_OneSided_Supplement_degrees

set_option autoImplicit false

namespace WeakGraphOracles.OneSided.Supplement

/-- Lemma 6.1 (= informal Theorem 5), printed p. 12 (PDF p. 13). `P_d^+`: at least
`n/2` vertices have degree at least `d`; farness is in `dist⊕`.
(1) Upper bound: there is a universal `C > 0` such that for every integer
`d ≥ 1` and every `ε ∈ (0,1]`, `P_d^+` is two-sided error testable in GEN1 with
`q ≤ C d² (1 + ln(1/ε)) / ε²` queries (the `Õ(d²/ε²)` of the source, with the
logarithmic factor of its proof in Section 7.7), one bound for all `n`.
(2) Lower bound: for every `d ≥ 1` and `0 < ε < 1/3`, for all large `n`, every
one-sided error `ε`-tester for `P_d^+`, even in GEN2, makes at least `n/8`
queries. -/
theorem lemma_6_1 :
    (∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ q : ℕ, (q : ℝ) ≤ C * (d : ℝ) ^ 2 * (1 + Real.log (1 / ε)) / ε ^ 2 ∧
        ∀ n : ℕ, ∃ A : Policy n q,
          TwoSidedCorrect (fun G : SimpleGraph (Fin n) => oracle G)
            (fun G => DegreeThreshold d G)
            (DistFar (fun G' => DegreeThreshold d G') ε) A) ∧
    ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 / 3 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (q : ℕ) (A : GEN2Policy n q),
        OneSidedCorrect (fun G : SimpleGraph (Fin n) => oracle2 G)
            (fun G => DegreeThreshold d G)
            (DistFar (fun G' => DegreeThreshold d G') ε) A →
          (n : ℝ) / 8 ≤ q := by sorry

end WeakGraphOracles.OneSided.Supplement
