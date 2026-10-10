-- Prove2me | Theorems.Thm_RieszMF_Linear_proposition_3_8
-- name    : RieszMF.Linear.proposition_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:59.884218+00:00
-- url     : https://prove2.me/theorems/4130f1ad-82d1-4093-ad20-6dd79c1bd40b
-- title:
--   Proposition 3.8, pp. 13–14 — $\|\mu^t\|_{L^q}\le(K(q)/K(p))^{d/2}(4\pi\sigma t/(1/p-1/q))^{-\frac d2(\frac1p-\frac1q)}\|\mu^0\|_{L^p}$
-- statement:
--   Let $d\ge3$, $0\le s<d-2$, $\sigma>0$, let $\mathbb M$ satisfy $\mathbb M\xi\cdot\xi\le0$ and let $\mathsf g$ be an admissible potential with radius $r_0$.
--   Let $\mu\in C([0,\infty);L^1\cap L^\infty)$ be a mild solution (3.1) of (1.5) with $\mu|_{t=0}=\mu^0$, and, if $\mathbb M:\nabla^{\otimes2}\mathsf g$ does not vanish identically on $\mathbb R^d\setminus\{0\}$, assume $\mu\ge0$. Let $1\le p\le q\le\infty$. Then for all $t>0$
--   $$\|\mu^t\|_{L^q}\le\Big(\frac{K(q)}{K(p)}\Big)^{d/2}\Big(\frac{4\pi\sigma t}{1/p-1/q}\Big)^{-\frac d2(\frac1p-\frac1q)}\|\mu^0\|_{L^p},\qquad K(r)=\frac{r'^{1/r'}}{r^{1/r}},$$
--   with $r'$ the Hölder conjugate of $r$.
--
--   The solution of the nonlinear equation decays like the heat equation; with $p=1$, $q=\infty$ this gives $\|\mu^t\|_{L^\infty}\le(4\pi\sigma t)^{-d/2}$, the decay that makes the prefactors of the Gronwall argument integrable in time.
--
--   **Formalization Note.** $K(1)=K(\infty)=1$ (the limits of $r'^{1/r'}/r^{1/r}$), and for $p=q$ the middle factor is $1$ (exponent $0$); both are written as explicit cases. $1/\infty=0$. The norms are compared in $[0,\infty]$.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, pp. 13–14, Proposition 3.8, (3.22), (3.23)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem proposition_3_8 (d : ℕ) (hd : 3 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d - 2)
    (σ : ℝ) (hσ : 0 < σ) (M : Matrix (Fin d) (Fin d) ℝ) (hM : NegSemidef M)
    (g : E d → ℝ) (r₀ : ℝ) (hg : Admissible d s M g r₀)
    (μ0 : E d → ℝ) (μ : ℝ≥0 → E d → ℝ) (hμ : IsMildSolution d σ M g μ0 μ)
    (hsign : (∃ x : E d, x ≠ 0 ∧ frob M g x ≠ 0) → ∀ t, ∀ᵐ x ∂volume, 0 ≤ μ t x)
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q) (t : ℝ≥0) (ht : 0 < t) :
    eLpNorm (μ t) q volume ≤
      ENNReal.ofReal ((carlenLossK q / carlenLossK p) ^ ((d : ℝ) / 2) *
        (if p = q then 1 else
          (4 * Real.pi * σ * t / ((p⁻¹).toReal - (q⁻¹).toReal)) ^
            (-((d : ℝ) / 2) * ((p⁻¹).toReal - (q⁻¹).toReal))))
        * eLpNorm μ0 p volume := by sorry

end RieszMF.Linear
