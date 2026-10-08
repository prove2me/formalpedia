-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_lemma_5_1_12
-- name    : SmoothedSimplex.TwoPhase.lemma_5_1_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:28:27.052692+00:00
-- url     : https://prove2.me/theorems/8c13874a-47d4-44da-8a0e-398580c37f31
-- title:
--   Lemma 5.1.12 (Probability of bad geometry)
-- statement:
--   For independent Gaussian $a_i\in\mathbb R^d$ with centers of norm at most one, $n>d\ge3$ and $\sigma>0$, the probability that some set $L$ of $\lfloor d/2-1\rfloor$ indices and some $j_0\notin L$ have unusually small height is at most
--   $$\Pr\!\left[\exists L,j_0:\operatorname{dist}(a_{j_0},\operatorname{Span}(A_L))\le\sqrt d\,\kappa_0\left(1+\frac{\lceil d/2\rceil\max_i\|a_i\|}{h_0}\right)\right]\le n^{-d}+n^{-2.9d+1}.$$
--   The event supplies the geometric exceptional case in Lemma 5.1.1.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 5.1.12, printed p. 66, PDF p. 66

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Lemma 5.1.12 (Probability of bad geometry), printed p. 66, PDF p. 66, under all conditions of Lemma 5.1.1. Formalization Note: `[n]` is `Fin n`; probability measures use product Gaussian laws. -/
theorem lemma_5_1_12 {n d : ℕ} (hn : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (hc : ∀ i, ‖c i‖ ≤ 1) (σ : ℝ) (hσ : 0 < σ) :
    ((gaussianFamily c σ) {a | ∃ L ∈ Finset.univ.powersetCard
      (Nat.floor (((d : ℝ) / 2) - 1)), ∃ j : Fin n, j ∉ L ∧
      height a L j ≤ Real.sqrt d * kappaZero n d σ *
        (1 + (Nat.ceil ((d : ℝ) / 2) : ℝ) *
          (sSup (Set.range (fun i : Fin n => ‖a i‖))) / heightZero n σ)}).toReal ≤
      (n : ℝ) ^ (-(d : ℝ)) + (n : ℝ) ^ (-(2.9 : ℝ) * d + 1) := by sorry

end SmoothedSimplex.TwoPhase
