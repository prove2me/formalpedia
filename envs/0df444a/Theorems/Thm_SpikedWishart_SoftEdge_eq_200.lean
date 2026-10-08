-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_eq_200
-- name    : SpikedWishart.SoftEdge.eq_200
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:39:58.719614+00:00
-- url     : https://prove2.me/theorems/f506da5b-9045-48ac-a451-d6b39b890696
-- title:
--   (200), p. 1676 — ∫₀^∞𝓗∞(u+y)𝓙∞(v+y)dy − ∫₀^∞e^{−ε(u+y)}Ai(u+y)Ai(v+y)e^{ε(v+y)}dy = Σ_m e^{−εu}s^{(m)}(u)t^{(m)}(v)e^{εv}
-- statement:
--   Let $k\ge1$ and $\varepsilon>0$, and let $\mathcal H_\infty,\mathcal J_\infty$ be defined by (120), (122) with $\Gamma_\infty$ having its vertex in $(-\varepsilon,0)$ and $\Sigma_\infty$ its vertex in $(-\infty,-\varepsilon)$, so that $\mathrm{Re}(a-b)>0$ for $a\in\Gamma_\infty$, $b\in\Sigma_\infty$. Then for all real $u,v$,
--   $$
--   \int_0^\infty\mathcal H_\infty(u+y)\mathcal J_\infty(v+y)\,dy-\int_0^\infty e^{-\varepsilon(u+y)}\mathrm{Ai}(u+y)\mathrm{Ai}(v+y)e^{\varepsilon(v+y)}\,dy=\sum_{m=1}^ke^{-\varepsilon u}s^{(m)}(u)\,t^{(m)}(v)\,e^{\varepsilon v}.
--   $$
--
--   After cancelling the factors $e^{\mp\varepsilon}$, this identifies the limit kernel of the steepest-descent analysis with the kernel $A+\sum_{m=1}^ks^{(m)}\otimes t^{(m)}$ whose Fredholm determinant is $F_k$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1676, §3.3, (200)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open MeasureTheory

namespace SpikedWishart.SoftEdge

theorem eq_200 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (cH cJ : ℝ) (hcH0 : -ε < cH)
    (hcH1 : cH < 0) (hcJ : cJ < -ε) (u v : ℝ) :
    (∫ y in Set.Ioi (0 : ℝ), Hinf ε k cH (u + y) * Jinf ε k cJ (v + y)) -
        (∫ y in Set.Ioi (0 : ℝ),
          ((Real.exp (-ε * (u + y)) * Ai (u + y) * Ai (v + y) * Real.exp (ε * (v + y)) : ℝ) : ℂ)) =
      ∑ m ∈ Finset.Icc 1 k,
        ((Real.exp (-ε * u) * sFn m u * tFn m v * Real.exp (ε * v) : ℝ) : ℂ) := by sorry

end SpikedWishart.SoftEdge
