-- Prove2me | Theorems.Thm_VecBalPoly_proposition_5_1
-- name    : VecBalPoly.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:18:57.133517+00:00
-- url     : https://prove2.me/theorems/59e2ab01-8744-41d4-8d49-bd12ed9a763d
-- title:
--   Proposition 5.1 — invariants after every cleanup and termination after $O(n^7)$ updates
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have columns of Euclidean norm at most $1$, with $n>K=16$. After initialization and after every cleanup of Algorithm 2.2, the state satisfies
--   $$d_i=0\ \text{for large rows},\qquad u_{i\sigma}\le0\ \text{for medium pairs},\qquad L<2.$$
--   Moreover there is an absolute constant $C$ such that every run prefix makes at most $Cn^7$ updates, and a prefix whose last state still has $s>K$ can be continued: a direction with the guarantees of Lemma 2.1 exists there. Hence the algorithm reaches $s\le K$ after $O(n^7)$ updates.
--
--   This is the analytic core of the paper: it keeps the hypotheses of Lemma 2.1 valid at every iteration and bounds the number of iterations.
--
--   Differences from the source:
--   - generalization: the states of Algorithm 2.2, whose step 1 computes h by the procedure of Lemma 2.1 → every prefix run whose directions are any vectors meeting Lemma 2.1's conclusion (GoodDir); reason: the paper's procedure returns such vectors (Lemma 2.1), so its runs are among these; the proof uses only those guarantees
--   - reading: no hypothesis on A printed in this statement → columns of Euclidean norm at most 1 and n > K; reason: the standing hypothesis of Theorem 1.1, under which Algorithm 2.2 runs; for n ≤ K the algorithm makes no update
--   - reading: "The algorithm reaches s ≤ K after O(n⁷) updates" → ∃ C (before m, n, A): every prefix run has N ≤ Cn⁷, and a prefix ending with s > K extends by a good direction; reason: the proof's "every finite prefix has O(n⁷) updates, so the algorithm must terminate" (p.12); for a relation, reaching s ≤ K also needs that no run gets stuck
--   - generalization: m ≥ 1 (the standing assumption of Theorem 1.1) → m = 0 also allowed; reason: with no rows there are no row constraints and the row sums are empty; the source's cases m ≥ 1 are included unchanged
--   - encoding: row, column and sign indices i ∈ [m], j ∈ [n], σ ∈ {−1, 1} → Fin m, Fin n (0-based) and σ : Bool with sgn true = 1, sgn false = −1; reason: Lean conventions; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Proposition 5.1, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_VecBalPoly_IsPrefixRun

namespace VecBalPoly

/-- **Proposition 5.1 (invariants and termination).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Proposition 5.1, p.11 (PDF p.12): "After initialization and after every cleanup in
Algorithm 2.2, the state satisfies di = 0 for large rows, uiσ ≤ 0 for medium pairs, L < 2. The
algorithm reaches s ≤ K after O(n⁷) updates."

**Formalization Note** States after initialization and after cleanups are the states `sts k`,
`k ≤ N`, of a prefix run (any directions meeting Lemma 2.1's conclusion). "Reaches `s ≤ K`
after `O(n⁷)` updates" is: one constant `C` (uniform in `m, n, A`) bounds the number of
updates of every prefix by `Cn⁷`, and a prefix whose last state still has `s > K` can be
continued (a direction with Lemma 2.1's guarantees exists). -/
theorem proposition_5_1 :
    ∃ C : ℝ, ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), (∀ j, ∑ i, A i j ^ 2 ≤ 1) →
      K < (n : ℝ) →
      ∀ (N : ℕ) (sts : ℕ → St m n) (hs : ℕ → Fin n → ℝ), IsPrefixRun A N sts hs →
        (∀ k ≤ N, (∀ i, IsLarge A (sts k) i → d A (sts k) i = 0) ∧
          (∀ i σ, IsMedium A (sts k) i → u A (sts k) i σ ≤ 0) ∧ L A (sts k) < 2) ∧
        (N : ℝ) ≤ C * (n : ℝ) ^ 7 ∧
        (K < ((sts N).V.card : ℝ) → ∃ h : Fin n → ℝ, GoodDir A (sts N) h) := by sorry

end VecBalPoly
