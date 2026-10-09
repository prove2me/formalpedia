-- Prove2me | Theorems.Thm_TaitTobin_Outerplanar_lemma_3
-- name    : TaitTobin.Outerplanar.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:52.725742+00:00
-- url     : https://prove2.me/theorems/03a07d48-ba99-4df3-92b1-b6559328e4a5
-- title:
--   Lemma 3, p. 5 — an outerplanar spectral maximizer on n ≥ 3 vertices has λ₁ > √(n − 1)
-- statement:
--   Let $n \ge 3$ and let $G$ be an outerplanar graph on $n$ vertices whose spectral radius $\lambda_1(G)$ (the largest adjacency eigenvalue) is maximum among all outerplanar graphs on the same $n$ vertices. Then
--   $$\lambda_1(G) > \sqrt{n-1}.$$
--
--   The bound compares $G$ with the star $K_{1,n-1}$, and is the quantitative input for Lemma 4.
--
--   **Formalization Note** The hypothesis $n \ge 3$ is added: for $n = 2$ the maximizer is $K_2$, with $\lambda_1 = 1 = \sqrt{n-1}$, and for $n = 1$, $\lambda_1 = 0$, so the strict inequality fails. The paper's proof ("the star is a strict subgraph of other outerplanar graphs") needs $n \ge 3$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 5, Lemma 3

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace TaitTobin.Outerplanar

open Classical WangKangXue.SpectralTuran

/-- Lemma 3, p. 5: for `n ≥ 3`, an outerplanar graph on `n` vertices of maximum spectral radius has
`λ₁ > √(n - 1)`. -/
theorem lemma_3 {n : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsSpecMax IsOuterplanar G) :
    Real.sqrt ((n : ℝ) - 1) < specRad G := by sorry
end TaitTobin.Outerplanar
