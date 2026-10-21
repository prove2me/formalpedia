-- Prove2me | Theorems.Thm_RegOTQuant_TwiceDiff_theorem_3_8
-- name    : RegOTQuant.TwiceDiff.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:07.198368+00:00
-- url     : https://prove2.me/theorems/9ac81eb2-c3e4-4394-abf6-c4c746abfeb1
-- title:
--   Theorem 3.8, p. 14, corrected — entropic and f-divergence rates
-- statement:
--   Let $\pi^*$ be an optimal coupling of $N\ge1$ finite-second-moment marginals on closed convex Euclidean sets. Suppose $c$ is $C^2$ near their product and satisfies the two-sided bound $|D^2c(x)[w,w]|\le B\|w\|^2$ for all $x$ in the product and all ambient $w$, with $B\ge0$. Suppose also that $\pi^*$ satisfies $\operatorname{quant}_2(C,\alpha)$ for $C>0$ and $0<\alpha\le1$.
--
--   For $f(t)=t\log t$ and $0<\varepsilon\le1$,
--
--   $$\mathrm{OT}_{f,\varepsilon}-\mathrm{OT}\le\frac{N-1}{2\alpha}\varepsilon\log(1/\varepsilon)+8BC^2\varepsilon.$$
--
--   If $N=2$, $f(t)=t\varphi(t)$ for $t>0$, and $\varphi$ is nondecreasing and concave there, put $\beta=1/(2\alpha)$ and $\widetilde f(t)=t\varphi(t^\beta)$. If $\widetilde f$ is strictly increasing on $[x_0,\infty)$ for $x_0\ge0$, its inverse value $S_\varepsilon=\widetilde f^{-1}(1/\varepsilon)$ satisfies $S_\varepsilon\to\infty$ and $\varepsilon S_\varepsilon\to0$ as $\varepsilon\downarrow0$. For the stated positive $\varepsilon$ with $\varepsilon x_0\le1$ and $S_\varepsilon\ge1$,
--
--   $$\mathrm{OT}_{f,\varepsilon}-\mathrm{OT}\le\frac{8BC^2+1}{S_\varepsilon}.$$
--
--   The squared constant and two-sided ambient Hessian condition correct the printed theorem. The result bounds regularization bias from a joint-plan quantization rate.
--
--   **Formalization Note** The generator $f$ in the second part has the §2.1 strict convexity, lower-boundedness, normalization, and superlinearity conditions. The parameter condition uses $\varepsilon x_0\le1$ so that $x_0=0$ is meaningful.
-- source:
--   Eckstein & Nutz, Convergence rates for regularized optimal transport via quantization, arXiv:2208.14391v3, p. 14, Theorem 3.8, with corrections to (3.4) and 8BC

import Mathlib
import Definitions.Def_RegOTQuant_TwiceDiff_Setting

open MeasureTheory Filter Set

namespace RegOTQuant.TwiceDiff

/-- Theorem 3.8, p. 14, corrected: (3.4) is two-sided for every ambient
 direction and the two printed factors 8BC are 8BC². -/
theorem theorem_3_8 {N : ℕ} {d : Fin N → ℕ}
    (Xs : ∀ i : Fin N, Set (Fi d i)) (μ : ∀ i : Fin N, Measure (Fi d i))
    (c : E d → ℝ) (πs : Measure (E d)) (B C α : ℝ)
    (hset : Setting Xs μ c) (hB : 0 ≤ B) (hH : HessBound Xs c B)
    (hopt : IsOptimal c μ πs) (hquant : Quant2 (X Xs) πs C α)
    (hα : 0 < α ∧ α ≤ 1) (hC : 0 < C) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      OTreg (fun x : ℝ => x * Real.log x) ε c μ ≤
        (((OTval c μ + ((N : ℝ) - 1) / (2 * α) * ε * Real.log (1 / ε)
          + 8 * B * C ^ 2 * ε) : ℝ) : EReal)) ∧
    (N = 2 → ∀ (f φ : ℝ → ℝ) (x0 : ℝ),
      FStanding f →
      (∀ x : ℝ, 0 < x → f x = x * φ x) →
      MonotoneOn φ (Ioi 0) → ConcaveOn ℝ (Ioi 0) φ →
      0 ≤ x0 → StrictMonoOn (ftilde φ (1 / (2 * α))) (Ici x0) →
      Tendsto (fun ε : ℝ => Sinv φ (1 / (2 * α)) x0 ε)
        (nhdsWithin 0 (Ioi 0)) atTop ∧
      Tendsto (fun ε : ℝ => ε * Sinv φ (1 / (2 * α)) x0 ε)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
      ∀ (ε S : ℝ), 0 < ε → ε * x0 ≤ 1 → x0 ≤ S →
        ftilde φ (1 / (2 * α)) S = 1 / ε → 1 ≤ S →
        OTreg f ε c μ ≤
          (((OTval c μ + (8 * B * C ^ 2 + 1) / S) : ℝ) : EReal)) := by sorry

end RegOTQuant.TwiceDiff
