-- Prove2me | Theorems.Thm_RieszMF_Linear_corollary_5_6
-- name    : RieszMF.Linear.corollary_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:17.044793+00:00
-- url     : https://prove2.me/theorems/920e119f-8cba-4318-a7d1-6c172d394371
-- title:
--   Corollary 5.6, pp. 23–24 — $\iint(-\Delta\mathsf g)(x-y)\,d(\mu_N-\mu)^{\otimes2}\ge-C(1+\|\mu\|_{L^\infty})N^{-\min\{2,d-s-2\}/\min\{s+4,d\}}$
-- statement:
--   Let $d\ge3$ and $0\le s<d-2$. Let $\mathsf g$ satisfy assumptions (i), (iii), (iv), (vi) and (viii). There is a constant $C>0$ depending only on $s$, $d$ and $\mathsf g$ such that for every $N\ge1$, every pairwise distinct $x_N\in(\mathbb R^d)^N$ and every $\mu\in\mathcal P(\mathbb R^d)\cap L^\infty(\mathbb R^d)$,
--   $$\int_{(\mathbb R^d)^2\setminus\triangle}(-\Delta\mathsf g)(x-y)\,d\Big(\frac1N\sum_{i=1}^N\delta_{x_i}-\mu\Big)^{\otimes2}(x,y)\ge-C(1+\|\mu\|_{L^\infty})N^{-\frac{\min\{2,d-s-2\}}{\min\{s+4,d\}}}.$$
--
--   The left side is the term that the Itô correction $\sigma\Delta$ contributes to the evolution of the modulated energy; the corollary says it has the good sign up to a vanishing error.
--
--   **Formalization Note.** The hypotheses are exactly the five printed assumptions. The printed proof applies (5.11) to $-\Delta\mathsf g$ when $0\le s\le d-4$, which uses the superharmonicity of $-\Delta\mathsf g$ near $0$; this is not among the listed assumptions (it holds for the model potentials). The statement is posed as printed, for every $N\ge1$ (for small $N$ a fixed smearing radius gives a bound the constant absorbs).
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, pp. 23–24, Corollary 5.6, (5.18)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem corollary_5_6 (d : ℕ) (hd : 3 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d - 2)
    (g : E d → ℝ) (r₀ : ℝ) (h1 : AssumpI g) (h3 : AssumpIII g r₀) (h4 : AssumpIV d s g)
    (h6 : AssumpVI d s g) (h8 : AssumpVIII d s g r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ x : Fin N → E d, Pairwise (fun i j => x i ≠ x j) →
      ∀ μ : E d → ℝ, IsProbDensityLinfty μ →
        -C * (1 + lpNorm μ ⊤) * (N : ℝ) ^ (-(min 2 ((d : ℝ) - s - 2) / min (s + 4) d))
          ≤ offDiag N (fun a b => -Δ g (a - b)) x μ := by sorry

end RieszMF.Linear
