-- Prove2me | Theorems.Thm_VecBalPoly_lemma_3_2
-- name    : VecBalPoly.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:19:10.548488+00:00
-- url     : https://prove2.me/theorems/5be12384-db72-4554-b4d0-ce2c92ffcd13
-- title:
--   Lemma 3.2 — the cleanup lemma
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have columns of Euclidean norm at most $1$, with $n>K$.
--   1. After the initial cleanup, $L\le2/K<1$ and $\Phi=0$; moreover every $d_i=0$ and every medium barrier satisfies $u_{i\sigma}<-1$ (all medium rows are newly medium at initialization).
--   2. Consider any later cleanup of a run, from the state right after an update to the next state. Suppose that before cleanup $d_i=0$ for every large row and $u_{i\sigma}\le0$ for every medium row and both signs. Then:
--      1. every tracked row sum $d_i$ is unchanged;
--      2. the barriers of rows that remain medium do not increase;
--      3. every newly medium barrier (a row large before and medium after) is strictly below $-1$;
--      4. the potential $\Phi$ does not increase.
--
--   Cleanup is where rows change class; this lemma shows it never breaks the invariants of Proposition 5.1.
--
--   Differences from the source:
--   - generalization: the states of Algorithm 2.2, whose step 1 computes h by the procedure of Lemma 2.1 → every prefix run whose directions are any vectors meeting Lemma 2.1's conclusion (GoodDir); reason: the paper's procedure returns such vectors (Lemma 2.1), so its runs are among these; the proof uses only those guarantees
--   - reading: no hypothesis on A printed in this statement → columns of Euclidean norm at most 1 and n > K; reason: the standing hypothesis of Theorem 1.1, under which Algorithm 2.2 runs; for n ≤ K the algorithm makes no update
--   - reading: "After the initial cleanup, L ≤ 2/K < 1 and Φ = 0" → also d_i = 0 for every row and u_{iσ} < −1 for every medium row of the initial cleanup; reason: the initial case of items 1 and 3 ("At initialization, all medium rows are treated as newly medium", p.5; App. A, p.13), which Proposition 5.1 uses for "the bounds hold initially by Lemma 3.2"
--   - reading: "before cleanup", "rows that remain medium", "newly medium" → the state preState after update k versus sts (k+1); medium in both; large in preState and medium after; reason: the classes before a cleanup are those of the previous cleanup
--   - generalization: m ≥ 1 (the standing assumption of Theorem 1.1) → m = 0 also allowed; reason: with no rows there are no row constraints and the row sums are empty; the source's cases m ≥ 1 are included unchanged
--   - encoding: row, column and sign indices i ∈ [m], j ∈ [n], σ ∈ {−1, 1} → Fin m, Fin n (0-based) and σ : Bool with sgn true = 1, sgn false = −1; reason: Lean conventions; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma 3.2, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_VecBalPoly_Phi
import Definitions.Def_VecBalPoly_IsPrefixRun

namespace VecBalPoly

/-- **Lemma 3.2 (cleanup lemma).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma 3.2, p.7 (PDF p.8): "After the initial cleanup, L ≤ 2/K < 1 and Φ = 0. Suppose that,
before cleanup, di = 0 for every large row i, and uiσ ≤ 0 for every medium row i and both signs
σ ∈ {−1, 1}. Then cleanup satisfies: 1. Every tracked row sum di remains unchanged. 2. The safety
barriers of rows that remain medium do not increase. 3. Every newly medium barrier is strictly
below −1. 4. The spectral potential Φ does not increase."

**Formalization Note** Part 1 is the initial cleanup `s₀`. It also records `dᵢ = 0` and the
initial case of item 3 (all medium rows of `s₀` are newly medium, p.5), which Proposition 5.1
uses ("The bounds hold initially by Lemma 3.2"). Part 2 is every later cleanup of a prefix run:
`pre` is the state right after the update and `sts (k+1)` the state after its cleanup. A row
"remains medium" when it is medium in both, and is "newly medium" when it was large in `pre`. -/
theorem lemma_3_2 :
    (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), (∀ j, ∑ i, A i j ^ 2 ≤ 1) → K < (n : ℝ) →
      L A (cleanup A true (initState A)) ≤ 2 / K ∧ Phi A (cleanup A true (initState A)) = 0 ∧
      (∀ i, d A (cleanup A true (initState A)) i = 0) ∧
      (∀ i σ, IsMedium A (cleanup A true (initState A)) i →
        u A (cleanup A true (initState A)) i σ < -1)) ∧
    (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), (∀ j, ∑ i, A i j ^ 2 ≤ 1) → K < (n : ℝ) →
      ∀ (N : ℕ) (sts : ℕ → St m n) (hs : ℕ → Fin n → ℝ), IsPrefixRun A N sts hs →
      ∀ k < N,
        (∀ i, IsLarge A (preState (sts k) (hs k)) i → d A (preState (sts k) (hs k)) i = 0) →
        (∀ i σ, IsMedium A (preState (sts k) (hs k)) i →
          u A (preState (sts k) (hs k)) i σ ≤ 0) →
        (∀ i, d A (sts (k + 1)) i = d A (preState (sts k) (hs k)) i) ∧
        (∀ i σ, IsMedium A (preState (sts k) (hs k)) i → IsMedium A (sts (k + 1)) i →
          u A (sts (k + 1)) i σ ≤ u A (preState (sts k) (hs k)) i σ) ∧
        (∀ i σ, IsLarge A (preState (sts k) (hs k)) i → IsMedium A (sts (k + 1)) i →
          u A (sts (k + 1)) i σ < -1) ∧
        Phi A (sts (k + 1)) ≤ Phi A (preState (sts k) (hs k))) := by sorry

end VecBalPoly
