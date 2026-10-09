-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_pineapple_lower_bound
-- name    : TaitTobin.Irregularity.pineapple_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:56.475513+00:00
-- url     : https://prove2.me/theorems/52e1d16e-0c05-48f1-8c82-bbe3b137d680
-- title:
--   Proof of Lemma 16, p. 14 — λ₁(H) − 2e(H)/n ≥ n/4 − 3/2 for H = PA(⌈n/2⌉ + 1, ⌊n/2⌋ − 1)
-- statement:
--   Let $n \ge 2$ and let $H = PA(\lceil n/2\rceil + 1, \lfloor n/2\rfloor - 1)$ be the pineapple whose clique has $\lceil n/2\rceil + 1$ vertices and which has $\lfloor n/2\rfloor - 1$ pendant vertices, so that $H$ has $n$ vertices. Then
--   $$\lambda_1(H) - \frac{2e(H)}{n} \ge \frac{n}{4} - \frac{3}{2}.$$
--
--   This exhibits a connected graph with large irregularity $\lambda_1 - d$, and so gives the lower bound in inequality (9) of the paper for every maximizer of $\lambda_1 - d$.
--
--   **Formalization Note** $\lceil n/2\rceil$ and $\lfloor n/2\rfloor$ are written as the natural-number quotients $(n+1)/2$ and $n/2$. The hypothesis $n \ge 2$ makes $\lfloor n/2\rfloor - 1$ a genuine natural number, so that $H$ has exactly $n$ vertices; the average degree of $H$ divides by its number of vertices, which is $n$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 14, proof of Lemma 16

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Proof of Lemma 16, p. 14: for `H = PA(⌈n/2⌉ + 1, ⌊n/2⌋ − 1)` on `n` vertices,
`λ₁(H) − 2e(H)/n ≥ n/4 − 3/2`. In `ℕ`, `⌈n/2⌉ = (n + 1) / 2` and `⌊n/2⌋ = n / 2`. -/
theorem pineapple_lower_bound (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) / 4 - 3 / 2 ≤
      specRad (pineapple ((n + 1) / 2 + 1) (n / 2 - 1)) -
        avgDeg (pineapple ((n + 1) / 2 + 1) (n / 2 - 1)) := by sorry
end TaitTobin.Irregularity
