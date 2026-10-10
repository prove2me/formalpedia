-- Prove2me | Theorems.Thm_TaitTobin_Planar_eq_7
-- name    : TaitTobin.Planar.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:43.702732+00:00
-- url     : https://prove2.me/theorems/307956d2-18ce-4311-b034-06689a5350fb
-- title:
--   Eq. (7), p. 9 — Σ_{y∼u, y∈S} v_y ≥ (v_u − ε)√(2n − 4) − 18/ε for u ∈ L
-- statement:
--   Fix $\varepsilon > 0$. For all sufficiently large $n$: let $G$ be a planar graph on $n$ vertices of maximum spectral radius among planar graphs on $n$ vertices, $\mathbf v$ a positive eigenvector for $\lambda_1(G)$ with maximum entry $1$, $x$ a vertex with $\mathbf v_x = 1$, and $L = \{z : \mathbf v_z > \varepsilon\}$, $S = V(G)\setminus L$. Then every $u \in L$ satisfies
--   $$\sum_{\substack{y \sim u \\ y \in S}} \mathbf v_y \ge (\mathbf v_u - \varepsilon)\sqrt{2n-4} - \frac{18}{\varepsilon}. \qquad (7)$$
--
--   Combined with (6), it shows that a vertex of $L$ with entry close to $1$ misses only a small part of the weight of $S$.
--
--   **Formalization Note** The threshold $N$ may depend on $\varepsilon$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 9, eq. (7)

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- Eq. (7), p. 9: for every `ε > 0` and all large `n`, in a planar graph of maximum spectral
radius, every `u ∈ L` satisfies `Σ_{y ∼ u, y ∈ S} v_y ≥ (v_u - ε)√(2n-4) - 18/ε`. -/
theorem eq_7 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ u ∈ Lset ε v,
          (v u - ε) * Real.sqrt (2 * (n : ℝ) - 4) - 18 / ε ≤
            ∑ y ∈ (Sset ε v).filter (fun y => G.Adj u y), v y := by sorry
end TaitTobin.Planar
