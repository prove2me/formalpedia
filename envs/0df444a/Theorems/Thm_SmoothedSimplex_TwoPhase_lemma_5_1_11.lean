-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_lemma_5_1_11
-- name    : SmoothedSimplex.TwoPhase.lemma_5_1_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:28:02.20671+00:00
-- url     : https://prove2.me/theorems/e7de0136-6d49-4901-8cda-ffc27e2a5384
-- title:
--   Lemma 5.1.11 (Big height, small coefficient)
-- statement:
--   Let $a_1,\ldots,a_d\in\mathbb R^d$ and let $u$ be a unit coefficient vector. If $\|\sum_i u_i a_i\|\le\kappa$ and the distance from $a_j$ to the span of the other $a_i$ exceeds $h$, with $\kappa,h>0$, then
--   $$|u_j|<\kappa/h.$$
--   This links a small singular direction to a nearly dependent column. **Formalization Note** The printed $\kappa_0,h_0$ are used as arbitrary positive thresholds; positivity follows from the paper's $\sigma>0$.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 5.1.11, printed p. 65, PDF p. 65

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Lemma 5.1.11 (Big height, small coefficient), printed p. 65, PDF p. 65. The positive κ and h are the paper’s κ₀ and h₀; positivity follows from σ>0 in the paper. Formalization Note: `[n]` is `Fin n`; probability measures use product Gaussian laws. -/
theorem lemma_5_1_11 {d : ℕ} (a : Fin d → Point d)
    (hd : 3 ≤ d) (u : EuclideanSpace ℝ (Fin d)) (j : Fin d) (κ h : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) (hu : ‖u‖ = 1)
    (hsmall : ‖∑ i : Fin d, (u i) • a i‖ ≤ κ)
    (hheight : h < height a (Finset.univ.erase j) j) :
    |u j| < κ / h := by sorry

end SmoothedSimplex.TwoPhase
