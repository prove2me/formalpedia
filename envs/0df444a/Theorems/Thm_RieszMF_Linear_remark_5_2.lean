-- Prove2me | Theorems.Thm_RieszMF_Linear_remark_5_2
-- name    : RieszMF.Linear.remark_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:06.366278+00:00
-- url     : https://prove2.me/theorems/eb843f23-cbfa-4ebe-a2a3-976da1bac7a8
-- title:
--   Remark 5.2, (5.10), p. 22 — $F_N(x_N,\mu)\ge-C(1+\|\mu\|_{L^\infty})N^{-\frac2{s+2}}(1+(\log N)(\mathbf 1_{s=0}+\mathbf 1_{s=d-2}))$
-- statement:
--   Let $d\ge3$, $0\le s\le d-2$, and let $\mathsf g$ satisfy assumptions (iii), (iv) and (vi) (superharmonic in $B(0,r_0)\setminus\{0\}$, derivative bounds, Fourier transform comparable to $|\xi|^{s-d}$). There is a constant $C>0$, depending only on $s$, $d$ and $\mathsf g$, such that for every $N\ge1$, every pairwise distinct configuration $x_N\in(\mathbb R^d)^N$ and every $\mu\in\mathcal P(\mathbb R^d)\cap L^\infty(\mathbb R^d)$ (with $\int\log(1+|x|)\,d\mu<\infty$ if $s=0$),
--   $$F_N(x_N,\mu)\ge-C(1+\|\mu\|_{L^\infty})N^{-\frac2{s+2}}\big(1+(\log N)(\mathbf 1_{s=0}+\mathbf 1_{s=d-2})\big).$$
--
--   The modulated energy is therefore almost nonnegative, which lets the Gronwall argument control $|F_N|$ by $F_N$.
--
--   **Formalization Note.** The remark follows from Proposition 5.1 with $\eta_i=N^{-1/(s+2)}$, which requires $\eta_i<\min\{\frac12,\frac{r_0}2\}$; for the finitely many smaller $N$ a fixed admissible $\eta$ gives a bound $-C'(1+\|\mu\|_{L^\infty})$ that the constant absorbs, so the statement is posed for every $N\ge1$.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 22, Remark 5.2, (5.10)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem remark_5_2 (d : ℕ) (hd : 3 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s ≤ d - 2)
    (g : E d → ℝ) (r₀ : ℝ) (h3 : AssumpIII g r₀) (h4 : AssumpIV d s g) (h6 : AssumpVI d s g) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ x : Fin N → E d, Pairwise (fun i j => x i ≠ x j) →
      ∀ μ : E d → ℝ, IsProbDensityLinfty μ → (s = 0 → LogMoment μ) →
        -C * (1 + lpNorm μ ⊤) * (N : ℝ) ^ (-(2 / (s + 2)))
            * (1 + Real.log N * ((if s = 0 then 1 else 0) + (if s = (d : ℝ) - 2 then 1 else 0)))
          ≤ modEnergy N g x μ := by sorry

end RieszMF.Linear
