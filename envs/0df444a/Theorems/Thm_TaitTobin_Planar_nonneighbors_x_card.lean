-- Prove2me | Theorems.Thm_TaitTobin_Planar_nonneighbors_x_card
-- name    : TaitTobin.Planar.nonneighbors_x_card
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:34.228975+00:00
-- url     : https://prove2.me/theorems/7ff0d354-98f9-4e59-a463-7c522b30c398
-- title:
--   §3, p. 10 — |{y ∈ S : y ≁ x}| ≤ 14εn
-- statement:
--   Fix $\varepsilon > 0$. For all sufficiently large $n$: let $G$ be a planar graph on $n$ vertices of maximum spectral radius among planar graphs on $n$ vertices, $\mathbf v$ a positive eigenvector for $\lambda_1(G)$ with maximum entry $1$, $x$ a vertex with $\mathbf v_x = 1$, and $S = \{z : \mathbf v_z \le \varepsilon\}$. Then
--   $$|\{y \in S : y \not\sim x\}| \le 14\varepsilon n.$$
--
--   So the vertex of maximum eigenvector entry is adjacent to almost all of $S$; this is the first of the two hubs of $K_2 + P_{n-2}$.
--
--   **Formalization Note** The threshold $N$ may depend on $\varepsilon$; the cardinality is compared as a real number with $14\varepsilon n$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 10, §3, "For n large enough, we have |{y ∈ S : y ≁ x}| ≤ 14εn."

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- §3, p. 10: for every `ε > 0` and all large `n`, in a planar graph of maximum spectral
radius, the vertex `x` with `v_x = 1` has `|{y ∈ S : y ≁ x}| ≤ 14εn`. -/
theorem nonneighbors_x_card : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        (((Sset ε v).filter (fun y => ¬ G.Adj y x)).card : ℝ) ≤ 14 * ε * n := by sorry
end TaitTobin.Planar
