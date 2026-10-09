-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_lemma_17
-- name    : TaitTobin.Irregularity.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:16.259468+00:00
-- url     : https://prove2.me/theorems/ba23e2fe-48d8-49b5-bac5-53be66145667
-- title:
--   Lemma 17, p. 14 — 0 ≤ (1/|N(x)|) Σ_{y∼x} (d_y − λ₁v_y) ≤ c₃√n
-- statement:
--   There are a constant $c_3$ and a threshold $N$ such that for every $n \ge N$ the following holds. Let $G$ be a connected graph on $n$ vertices maximizing $\lambda_1 - d$, and let $\mathbf v$ be a leading eigenvector of its adjacency matrix ($A\mathbf v = \lambda_1 \mathbf v$) with all entries positive and maximum entry $1$, attained at a vertex $x$. Writing $d_y$ for the degree of $y$ and $N(x)$ for the neighbourhood of $x$,
--   $$0 \le \frac{1}{|N(x)|}\sum_{y \sim x} \bigl(d_y - \lambda_1 \mathbf v_y\bigr) \le c_3 \sqrt n .$$
--
--   So on average the neighbours $y$ of $x$ satisfy $d_y \approx \lambda_1 \mathbf v_y$, up to $O(\sqrt n)$; this is what lets the proof find vertices whose degree and eigenvector entry are both large (Lemma 18).
--
--   **Formalization Note** The page prints $\sum_{y\sim x} d_y - \lambda_1 \mathbf v_y$; the proof (p. 15) shows that the summand is $d_y - \lambda_1\mathbf v_y$, which is what is stated. The eigenvector is any vector with $A\mathbf v = \lambda_1\mathbf v$, positive entries and entries at most $1$, and $x$ is any vertex with $\mathbf v_x = 1$; such a vector exists by the Perron–Frobenius theorem since $G$ is connected. The constant $c_3$ is chosen before $n$ and $G$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 14, Lemma 17 (proof on p. 15)

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Lemma 17, p. 14: there is a constant `c₃`, independent of `n`, such that for `n` large, every
maximizer `G` of `λ₁ − d` and every vertex `x` of maximum Perron entry `v_x = 1` satisfy
`0 ≤ (1/|N(x)|) ∑_{y∼x} (d_y − λ₁ v_y) ≤ c₃ √n`. -/
theorem lemma_17 : ∃ c₃ : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsIrregMax G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
      0 ≤ (∑ y ∈ G.neighborFinset x, ((G.degree y : ℝ) - specRad G * v y)) / (G.degree x : ℝ) ∧
      (∑ y ∈ G.neighborFinset x, ((G.degree y : ℝ) - specRad G * v y)) / (G.degree x : ℝ) ≤
        c₃ * Real.sqrt n := by sorry
end TaitTobin.Irregularity
