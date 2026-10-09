-- Prove2me | Theorems.Thm_TaitTobin_Outerplanar_lemma_4
-- name    : TaitTobin.Outerplanar.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:02.897924+00:00
-- url     : https://prove2.me/theorems/cd4794a5-59b8-463b-8c5c-cc4fb4070fe1
-- title:
--   Lemma 4, p. 6 — in an outerplanar spectral maximizer, d_u > v_u n − 11√n for every vertex u
-- statement:
--   Let $G$ be an outerplanar graph on $n$ vertices whose spectral radius $\lambda_1$ is maximum among all outerplanar graphs on the same $n$ vertices. Let $\mathbf v$ be an eigenvector of the adjacency matrix for $\lambda_1$ with all entries positive, normalized so that its maximum entry is $1$, and let $x$ be a vertex with $\mathbf v_x = 1$. Then every vertex $u$ satisfies
--   $$d_u > \mathbf v_u\, n - 11\sqrt n,$$
--   where $d_u$ is the degree of $u$.
--
--   The lemma ties large eigenvector entries to large degrees; applied at $u = x$ it shows that $x$ is adjacent to almost every vertex (Lemma 5).
--
--   **Formalization Note** The statement holds for every such $\mathbf v$ and every such $x$ (the paper fixes one choice arbitrarily); $x$ is part of the paper's standing normalization and is not used in the conclusion. No lower bound on $n$ is needed: for $n < 121$ the right-hand side is negative. A positive eigenvector exists because the maximizer is connected (Perron–Frobenius).
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 6, Lemma 4

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace TaitTobin.Outerplanar

open Classical WangKangXue.SpectralTuran

/-- Lemma 4, p. 6: in an outerplanar graph of maximum spectral radius, with Perron vector `v`
normalized to maximum entry `1`, every vertex `u` has `d_u > v_u n - 11√n`. -/
theorem lemma_4 {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsSpecMax IsOuterplanar G)
    (v : Fin n → ℝ) (hv : (G.adjMatrix ℝ).mulVec v = specRad G • v)
    (hpos : ∀ i, 0 < v i) (hle : ∀ i, v i ≤ 1) (x : Fin n) (hx : v x = 1) (u : Fin n) :
    v u * n - 11 * Real.sqrt n < (G.degree u : ℝ) := by sorry
end TaitTobin.Outerplanar
