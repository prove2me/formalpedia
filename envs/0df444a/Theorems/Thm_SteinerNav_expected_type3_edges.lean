-- Prove2me | Theorems.Thm_SteinerNav_expected_type3_edges
-- name    : SteinerNav.expected_type3_edges
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:38.94182+00:00
-- url     : https://prove2.me/theorems/7d01dc42-2205-414a-9f8b-5ea1dd644a2e
-- title:
--   Proof of Theorem 3, p.9 — $\mathbb E T\le n(n-m)/(m+1)\le n^2/m$ and $\Pr[T\le 4n^2/m]\ge 3/4$
-- statement:
--   Let $P\subset\mathbb R^d$ have $n\ge2$ points and let $1\le m\le n$. Choose the landmark set $Q$ uniformly among the $m$-subsets of $P$, and let $T$ be the number of type-3 edges, the pairs $s\neq t$ in $P$ with $\|s-t\|<\min_{q\in Q}\|q-t\|$. Then
--
--   1. $\displaystyle \mathbb E\,T\ \le\ n\,\frac{n-m}{m+1}$;
--   2. $\displaystyle n\,\frac{n-m}{m+1}\ \le\ \frac{n^2}{m}$;
--   3. $\displaystyle \Pr\Big[T\le\frac{4n^2}{m}\Big]\ \ge\ \frac34$.
--
--   These bound the number of type-3 edges in the construction of Theorem 3.
--
--   **Formalization Note** The expectation is the average of $T$ over all $m$-subsets of $P$, and the probability is the fraction of $m$-subsets satisfying the event.
--
--   Differences from the source:
--   - encoding: "ET ≤ Σ_{t∈P} EZ_t = n(n − m)/(m + 1)" → ET ≤ n(n − m)/(m + 1); reason: the middle term is the proof's route, and its value EZ_t = (n − m)/(m + 1) is the separate item expected_gap.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 3, p.9 (displays ET ≤ … ≤ n²/m and Pr[T ≤ 4n²/m] ≥ 3/4)

import Mathlib
import Definitions.Def_SteinerNav_constructionEdges

namespace SteinerNav

open scoped Classical in
/-- Proof of Theorem 3, `E T` and Markov: for `Q` uniform on the `m`-subsets of `P`, `1 ≤ m ≤ n = |P|`, the
number `T` of type-3 edges satisfies `E T ≤ n(n − m)/(m + 1) ≤ n²/m`, and `T ≤ 4n²/m` on at least `3/4` of
the `m`-subsets (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 3, p.9). -/
theorem expected_type3_edges {d : ℕ} (P : Finset (Pt d)) (hn : 2 ≤ P.card) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.card) :
    (∑ Q ∈ P.powersetCard m, ((type3Edges P Q).card : ℝ)) / ((P.powersetCard m).card : ℝ) ≤
        (P.card : ℝ) * ((P.card : ℝ) - m) / ((m : ℝ) + 1) ∧
      (P.card : ℝ) * ((P.card : ℝ) - m) / ((m : ℝ) + 1) ≤ (P.card : ℝ) ^ 2 / (m : ℝ) ∧
      (3 / 4 : ℝ) * ((P.powersetCard m).card : ℝ) ≤
        (((P.powersetCard m).filter fun Q =>
          ((type3Edges P Q).card : ℝ) ≤ 4 * (P.card : ℝ) ^ 2 / (m : ℝ)).card : ℝ) := by sorry

end SteinerNav
