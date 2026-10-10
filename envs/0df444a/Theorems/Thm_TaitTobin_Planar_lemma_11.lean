-- Prove2me | Theorems.Thm_TaitTobin_Planar_lemma_11
-- name    : TaitTobin.Planar.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:50:00.796545+00:00
-- url     : https://prove2.me/theorems/b24cae62-5934-4eba-b5a3-5a139419e304
-- title:
--   Lemma 11, p. 10 — a second vertex w ∈ L with v_w > 1 − 24ε adjacent to all but 94εn vertices of S
-- statement:
--   There is $\varepsilon_0 > 0$ such that for every $0 < \varepsilon < \varepsilon_0$ and all sufficiently large $n$ the following holds. Let $G$ be a planar graph on $n$ vertices of maximum spectral radius among planar graphs on $n$ vertices, $\mathbf v$ a positive eigenvector for $\lambda_1(G)$ with maximum entry $1$, $x$ a vertex with $\mathbf v_x = 1$, and $L = \{z : \mathbf v_z > \varepsilon\}$, $S = V(G)\setminus L$. Then there is a vertex $w \in L$ with $w \neq x$ such that
--   $$\mathbf v_w > 1 - 24\varepsilon \qquad\text{and}\qquad |\{y \in S : y \not\sim w\}| \le 94\varepsilon n.$$
--
--   This produces the second hub of $K_2 + P_{n-2}$.
--
--   **Formalization Note** The paper fixes $\varepsilon$ "whose exact value will be chosen later"; the lemma needs $\varepsilon$ small (for $\varepsilon \ge 1$ the set $L$ is empty), so $\varepsilon$ ranges below an unspecified $\varepsilon_0$, and the threshold for $n$ may depend on $\varepsilon$. The conclusion is packaged as the predicate `IsSecondHub` of the setting file.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 10, Lemma 11

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- Lemma 11, p. 10: for every sufficiently small `ε > 0` and all large `n`, in a planar graph of
maximum spectral radius there is `w ∈ L`, `w ≠ x`, with `v_w > 1 - 24ε` and
`|{y ∈ S : y ≁ w}| ≤ 94εn`. -/
theorem lemma_11 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∃ w : Fin n, IsSecondHub G ε v x w := by sorry
end TaitTobin.Planar
