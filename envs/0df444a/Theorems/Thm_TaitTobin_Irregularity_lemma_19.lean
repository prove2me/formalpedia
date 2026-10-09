-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_lemma_19
-- name    : TaitTobin.Irregularity.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:21.581566+00:00
-- url     : https://prove2.me/theorems/f547598f-1a45-4656-8693-219539a5f6ff
-- title:
--   Lemma 19, p. 17 (corrected) — large v_a v_b forces adjacency; small v_a v_b forbids a non-bridge edge
-- statement:
--   For every $\varepsilon > 0$ there is $N$ such that for every $n \ge N$ the following holds. Let $G$ be a connected graph on $n$ vertices maximizing $\lambda_1 - d$, and let $\mathbf v$ be a leading eigenvector with positive entries and maximum entry $1$. For any two distinct vertices $a \ne b$:
--
--   1. if $\mathbf v_a \mathbf v_b > \dfrac12 + n^{-1/2} + 5n^{-1}$, then $a$ and $b$ are adjacent;
--   2. if $\mathbf v_a \mathbf v_b < \dfrac12 - 3\varepsilon$ and the graph $G - ab$ obtained by deleting the pair $\{a,b\}$ is connected, then $a$ and $b$ are not adjacent.
--
--   The lemma converts eigenvector entries into adjacency: pairs of high-entry vertices are edges, and low-entry pairs are not edges unless the edge is needed for connectivity. Proposition 20 is built on it.
--
--   **Formalization Note** The page states the second half without the connectivity proviso, and then it is false: in a pineapple, a pendant vertex $p$ and the clique vertex $h$ it hangs from have $\mathbf v_h\mathbf v_p = 1/\lambda_1 \approx 2/n$, yet they are adjacent. The proof compares $G$ with $G - ab$, which is legitimate only when $G - ab$ is connected, since the maximum ranges over connected graphs; Proposition 20 applies it only to such edges (p. 19). Distinctness $a \ne b$ is added because the page's $x, y$ are meant to be two vertices (for $a = b$ of entry $1$ the first half would assert a loop). The page's vertex names $x, y$ are renamed $a, b$ to avoid a clash with the fixed vertex $x$. The proof works for every $\varepsilon > 0$ (the second half is vacuous once $\varepsilon \ge 1/6$).
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 17, Lemma 19 (proof pp. 17–18), corrected

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Lemma 19, p. 17, corrected: for every `ε > 0` and `n` large, in a maximizer `G` of `λ₁ − d`
with Perron vector `v` (maximum entry `1`), two distinct vertices `a, b` with
`v_a v_b > 1/2 + n^{-1/2} + 5n^{-1}` are adjacent; and two distinct vertices with
`v_a v_b < 1/2 − 3ε` are not adjacent, provided deleting the pair `ab` leaves `G` connected.
The printed lemma omits `a ≠ b` and the connectivity proviso, without which it is false
(a pendant edge of a pineapple). -/
theorem lemma_19 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsIrregMax G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → (∃ x : Fin n, v x = 1) →
      ∀ a b : Fin n, a ≠ b →
        (1 / 2 + 1 / Real.sqrt n + 5 / (n : ℝ) < v a * v b → G.Adj a b) ∧
        (v a * v b < 1 / 2 - 3 * ε → (G.deleteEdges {s(a, b)}).Connected → ¬ G.Adj a b) := by sorry
end TaitTobin.Irregularity
