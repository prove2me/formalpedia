-- Prove2me | Theorems.Thm_WangKangXue_SpectralTuran_lemma_2_7
-- name    : WangKangXue.SpectralTuran.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:29:03.111426+00:00
-- url     : https://prove2.me/theorems/a7edfbec-7ef8-4f57-8262-8ab0d33ed309
-- title:
--   Lemma 2.7 — balancing two parts of K_r(n_1, …, n_r) increases λ
-- statement:
--   For positive integers $n_1, \dots, n_r$ let $K_r(n_1,\dots,n_r)$ be the complete $r$-partite graph with parts of sizes $n_1,\dots,n_r$. If $n_i - n_j \ge 2$ for some $i, j$, then moving one vertex from the $i$-th part to the $j$-th part strictly increases the spectral radius:
--   $$
--   \lambda\big(K_r(n_1,\dots,n_i - 1,\dots,n_j + 1,\dots,n_r)\big) \ >\ \lambda\big(K_r(n_1,\dots,n_i,\dots,n_j,\dots,n_r)\big).
--   $$
--
--   Among complete $r$-partite graphs on $n$ vertices the Turán graph $T_{n,r}$ therefore has the largest spectral radius; the proof of Lemma 3.10 uses a quantitative version of this.
--
--   **Formalization Note** $K_r(n_1,\dots,n_r)$ is Mathlib's `completeMultipartiteGraph` with part $k$ equal to `Fin (m k)`. The positivity of all part sizes is the paper's convention for $K_r(n_1,\dots,n_r)$ (p. 3, "we assume that $n_1 \ge \dots \ge n_r > 0$"). The hypothesis is written $n_j + 2 \le n_i$ to avoid natural-number subtraction.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 3, Lemma 2.7 (from Feng, Li, Zhang and Stevanović, Gutman, Rehman)

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad

namespace WangKangXue.SpectralTuran

open Classical

/-- **Lemma 2.7** (Wang–Kang–Xue, arXiv:2203.10831v1, p. 3; Feng–Li–Zhang, Stevanović et al.).
For the complete `r`-partite graph `K_r(n_1, …, n_r)` with positive part sizes: if
`n_i − n_j ≥ 2`, then moving one vertex from part `i` to part `j` strictly increases the spectral
radius:
`λ(K_r(…, n_i − 1, …, n_j + 1, …)) > λ(K_r(…, n_i, …, n_j, …))`. -/
theorem lemma_2_7 (r : ℕ) (m : Fin r → ℕ) (hm : ∀ k, 0 < m k) (i j : Fin r)
    (hij : m j + 2 ≤ m i) :
    specRad (SimpleGraph.completeMultipartiteGraph (fun k : Fin r => Fin (m k))) <
      specRad (SimpleGraph.completeMultipartiteGraph
        (fun k : Fin r =>
          Fin (Function.update (Function.update m i (m i - 1)) j (m j + 1) k))) := by sorry

end WangKangXue.SpectralTuran
