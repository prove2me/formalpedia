-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_lemma_5_1_7
-- name    : SmoothedSimplex.TwoPhase.lemma_5_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:28:27.885218+00:00
-- url     : https://prove2.me/theorems/eb83bfb3-6ef1-4b55-9ddf-aa7b20225404
-- title:
--   Lemma 5.1.7 (Sum over j of Y^j_K)
-- statement:
--   For $n>d\ge3$, let the $a_i\in\mathbb R^d$ be independent Gaussian vectors of common standard deviation $\sigma>0$, centered at points of norm at most one. For every $(d-1)$-set $K$, let $Y_K^j$ indicate $\operatorname{dist}(a_j,\operatorname{Span}(A_K))\le h_0$. Then
--   $$\Pr\!\left[\sum_{j\notin K}Y_K^j\ge\left\lceil\frac{n-d+1}{2}\right\rceil\right]\le\left(\frac{4h_0}{\sigma}\right)^{\left\lceil(n-d+1)/2\right\rceil}.$$
--   This is the fixed-$K$ concentration estimate used by Lemma 5.1.8.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 5.1.7, printed p. 63, PDF p. 63

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Lemma 5.1.7 (Sum over j of Y^j_K), printed p. 63, PDF p. 63. The inherited assumptions are n>d≥3, σ>0, independent Gaussians, and center norms at most one. Formalization Note: `[n]` is `Fin n`; probability measures use product Gaussian laws. -/
theorem lemma_5_1_7 {n d : ℕ} (hn : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (hc : ∀ i, ‖c i‖ ≤ 1) (σ : ℝ) (hσ : 0 < σ)
    (K : Finset (Fin n)) (hK : K.card = d - 1) :
    ((gaussianFamily c σ) {a | (∑ j ∈ Finset.univ.filter (fun j : Fin n => j ∉ K),
      lowHeight a K j σ) ≥ Nat.ceil (((n : ℝ) - d + 1) / 2)}).toReal ≤
      (4 * heightZero n σ / σ) ^ (Nat.ceil (((n : ℝ) - d + 1) / 2)) := by sorry

end SmoothedSimplex.TwoPhase
