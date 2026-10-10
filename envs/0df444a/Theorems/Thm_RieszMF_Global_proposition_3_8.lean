-- Prove2me | Theorems.Thm_RieszMF_Global_proposition_3_8
-- name    : RieszMF.Global.proposition_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:52.294396+00:00
-- url     : https://prove2.me/theorems/5ec3ae57-a799-44ec-a3fd-f16c758c833e
-- title:
--   Proposition 3.8, pp. 13–14 — heat-type $L^p\to L^q$ decay of solutions of (1.5)
-- statement:
--   Let $d\ge3$, $0\le s<d-2$, $\sigma>0$, $\mathbb M$ with (1.2) and $\mathsf g$ admissible. Let $\mu\in C([0,\infty);L^1\cap L^\infty)$ be a mild solution of (1.5); if $\mathbb M:\nabla^{\otimes2}\mathsf g\not\equiv0$, assume $\mu\ge0$. Let $1\le p\le q\le\infty$. Then for all $t>0$,
--
--   $$\|\mu^t\|_{L^q}\le\Big(\frac{K(q)}{K(p)}\Big)^{d/2}\Big(\frac{4\pi\sigma t}{1/p-1/q}\Big)^{-\frac d2(\frac1p-\frac1q)}\|\mu^0\|_{L^p},\qquad K(r)=\frac{r'^{1/r'}}{r^{1/r}},$$
--
--   with $r'$ the Hölder conjugate of $r$. The solutions therefore decay like solutions of the heat equation; with $p=1$, $q=\infty$ this gives $\|\mu^t\|_{L^\infty}\lesssim(\sigma t)^{-d/2}$, the decay that makes the time integrals in the proof of Theorem 1.2 finite.
--
--   **Formalization Note** $K(1)=K(\infty)=1$ (the limiting values) and, for $p=q$, the middle factor is $1$ (its limit as $1/p-1/q\to0$); both are written as explicit cases. "$\mathbb M:\nabla^{\otimes2}\mathsf g\ne0$" is read as "not identically zero on $\mathbb R^d\setminus\{0\}$".
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, pp. 13–14, Proposition 3.8, (3.22)–(3.23)

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Proposition 3.8 (pp. 13–14), (3.22): for a solution `μ ∈ C([0, ∞); L¹ ∩ L^∞)` of (1.5)
(nonnegative if `𝕄 : ∇^{⊗2} g ≢ 0`), for `1 ≤ p ≤ q ≤ ∞` and `t > 0`,
`‖μ^t‖_{L^q} ≤ (K(q)/K(p))^{d/2} (4πσt/(1/p - 1/q))^{-(d/2)(1/p - 1/q)} ‖μ^0‖_{L^p}`. -/
theorem proposition_3_8 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → 0 ≤ s → s < (d : ℝ) - 2 →
    ∀ (σ : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (g : RieszMF.Linear.E d → ℝ) (r₀ : ℝ),
      0 < σ → RieszMF.Linear.NegSemidef M → Admissible d s M g r₀ →
    ∀ (μ0 : RieszMF.Linear.E d → ℝ) (μ : ℝ≥0 → RieszMF.Linear.E d → ℝ),
      IsMildSolution d σ M g μ0 μ →
      ((∃ x : RieszMF.Linear.E d, x ≠ 0 ∧ RieszMF.Linear.frob M g x ≠ 0) → ∀ t, ∀ᵐ x ∂volume, 0 ≤ μ t x) →
    ∀ p q : ℝ≥0∞, 1 ≤ p → p ≤ q →
    ∀ t : ℝ≥0, 0 < t →
      eLpNorm (μ t) q volume ≤
        ENNReal.ofReal ((RieszMF.Linear.carlenLossK q / RieszMF.Linear.carlenLossK p) ^ ((d : ℝ) / 2) *
          decayFactor d σ t p q) * eLpNorm μ0 p volume := by sorry

end RieszMF.Global
