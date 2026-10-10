-- Prove2me | Theorems.Thm_TaitTobin_Planar_lemma_9
-- name    : TaitTobin.Planar.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:35.088268+00:00
-- url     : https://prove2.me/theorems/f1be617c-2df1-4c3e-a990-98cf124df3bb
-- title:
--   Lemma 9, p. 9 — Σ_{z∈L} v_z ≤ ε√(2n − 4) + 18/ε and Σ_{z∈S} v_z ≤ (1 + 3ε)√(2n − 4)
-- statement:
--   Fix $\varepsilon > 0$. For all sufficiently large $n$: let $G$ be a planar graph on $n$ vertices of maximum spectral radius among planar graphs on $n$ vertices, $\mathbf v$ a positive eigenvector for $\lambda_1(G)$ with maximum entry $1$, $x$ a vertex with $\mathbf v_x = 1$, and $L = \{z : \mathbf v_z > \varepsilon\}$, $S = V(G)\setminus L$. Then
--   $$\sum_{z \in L} \mathbf v_z \le \varepsilon\sqrt{2n-4} + \frac{18}{\varepsilon} \quad (5) \qquad\text{and}\qquad \sum_{z \in S} \mathbf v_z \le (1+3\varepsilon)\sqrt{2n-4} \quad (6).$$
--
--   These bounds on the total eigenvector weight of each class are what forces the two hubs of the extremal graph to be adjacent to most of $S$.
--
--   **Formalization Note** The threshold $N$ may depend on $\varepsilon$. A positive Perron eigenvector exists because the maximizer is connected.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 9, Lemma 9, eqs. (5) and (6)

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- Lemma 9, p. 9: for every `ε > 0` and all large `n`, in a planar graph of maximum spectral
radius, `Σ_{z∈L} v_z ≤ ε√(2n-4) + 18/ε` (5) and `Σ_{z∈S} v_z ≤ (1 + 3ε)√(2n-4)` (6). -/
theorem lemma_9 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        (∑ z ∈ Lset ε v, v z) ≤ ε * Real.sqrt (2 * (n : ℝ) - 4) + 18 / ε ∧
          (∑ z ∈ Sset ε v, v z) ≤ (1 + 3 * ε) * Real.sqrt (2 * (n : ℝ) - 4) := by sorry
end TaitTobin.Planar
