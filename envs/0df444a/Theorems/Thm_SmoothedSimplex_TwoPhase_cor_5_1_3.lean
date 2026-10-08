-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_cor_5_1_3
-- name    : SmoothedSimplex.TwoPhase.cor_5_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:28:55.518977+00:00
-- url     : https://prove2.me/theorems/5f2f5363-3284-4e29-b8a4-fa4f7d6e6c39
-- title:
--   Corollary 5.1.3 (probability of κ in 𝒦)
-- statement:
--   Under the same Gaussian and sampling assumptions, let $\kappa=2^{\lfloor\log_2s_{\min}(A_{\mathcal I(A)})\rfloor}$ and let $\mathcal K$ be equation (36). Then
--   $$\Pr_{A,\mathcal I}[\kappa\notin\mathcal K]\le\frac{0.42}{\binom nd}.$$
--   This places the random condition scale in a short deterministic list with high probability.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Corollary 5.1.3, printed p. 61, PDF p. 61

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Corollary 5.1.3 (κ lies in 𝒦), printed p. 61, PDF p. 61, with independent uniform sampled d-sets. Formalization Note: `[n]` is `Fin n`; probability measures use product Gaussian laws. -/
theorem cor_5_1_3 {n d : ℕ} (hn : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (hc : ∀ i, ‖c i‖ ≤ 1) (σ : ℝ) (hσ : 0 < σ) :
    (((gaussianFamily c σ).prod (sampleLaw n d)) {p |
      scaleK p.1 (bestSample p.1 p.2) ∉ kappaGrid n d σ}).toReal ≤
        (0.42 : ℝ) / Nat.choose n d := by sorry

end SmoothedSimplex.TwoPhase
