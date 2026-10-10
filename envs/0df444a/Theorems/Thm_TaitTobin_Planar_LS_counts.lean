-- Prove2me | Theorems.Thm_TaitTobin_Planar_LS_counts
-- name    : TaitTobin.Planar.LS_counts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:40.113563+00:00
-- url     : https://prove2.me/theorems/a62fdd35-7cf6-4353-af5e-ecbb5ab31870
-- title:
--   §3, p. 8 — |L| ≤ 3√(2n−4)/ε, e(S, L) ≤ 2n − 4, e(S) ≤ 3n − 6, e(L) ≤ 9√(2n−4)/ε
-- statement:
--   Fix $\varepsilon > 0$. For all sufficiently large $n$ the following holds. Let $G$ be a planar graph on $n$ vertices of maximum spectral radius $\lambda_1$ among planar graphs on $n$ vertices, let $\mathbf v$ be an eigenvector of its adjacency matrix for $\lambda_1$ with all entries positive and maximum entry $1$, and let $x$ be a vertex with $\mathbf v_x = 1$. With $L = \{z : \mathbf v_z > \varepsilon\}$ and $S = V(G) \setminus L$,
--   $$|L| \le \frac{3\sqrt{2n-4}}{\varepsilon}, \qquad e(S,L) \le 2n-4, \qquad e(S) \le 3n-6, \qquad e(L) \le \frac{9\sqrt{2n-4}}{\varepsilon}.$$
--
--   These counts say that only $O(\sqrt n)$ vertices have large eigenvector entry and control the edges inside and between the two classes; they feed Lemma 9.
--
--   **Formalization Note** "For $n$ sufficiently large" is a threshold $N$ that may depend on $\varepsilon$. The vertex $x$ is the paper's standing normalization and is not used in the conclusion. A positive Perron eigenvector exists because the maximizer is connected.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 8, §3, the paragraph following the definition of L and S

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- §3, p. 8: for every `ε > 0` and all large `n`, in a planar graph of maximum spectral radius
with Perron vector `v` (maximum entry `1`, `v x = 1`), the sets `L = {z : v_z > ε}` and
`S = V(G) \ L` satisfy `|L| ≤ 3√(2n-4)/ε`, `e(S, L) ≤ 2n - 4`, `e(S) ≤ 3n - 6` and
`e(L) ≤ 9√(2n-4)/ε`. -/
theorem LS_counts : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ((Lset ε v).card : ℝ) ≤ 3 * Real.sqrt (2 * (n : ℝ) - 4) / ε ∧
          TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) ≤ 2 * n - 4 ∧
          TaitTobin.Outerplanar.eIn G (Sset ε v) ≤ 3 * n - 6 ∧
          (TaitTobin.Outerplanar.eIn G (Lset ε v) : ℝ) ≤ 9 * Real.sqrt (2 * (n : ℝ) - 4) / ε := by sorry
end TaitTobin.Planar
