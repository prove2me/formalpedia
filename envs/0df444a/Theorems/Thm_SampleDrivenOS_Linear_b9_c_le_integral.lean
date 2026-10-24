-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_b9_c_le_integral
-- name    : SampleDrivenOS.Linear.b9_c_le_integral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:33.125049+00:00
-- url     : https://prove2.me/theorems/31d9bfc0-dd7d-45dc-b1c3-3da0ee4df29c
-- title:
--   B.9, p. 36 — $c(p)\le\frac1p\int_0^1\frac{dy}{1/(p\alpha^*)-1+y(1-p\ln y)}-\alpha^*(1-p)$
-- statement:
--   Let $s\in(0,1)$, $p\in(0,1)$ and
--   $$c(p)=\sum_{i=1}^{\infty}\frac{p^{i-1}-p^i}{\tfrac1{ps}-1+p^i(1+i(1-p))}.$$
--   Then
--   $$c(p)\le\frac1p\int_0^1\frac{dy}{\tfrac1{ps}-1+y(1-p\ln y)}-s(1-p).$$
--
--   This compares the series $c(p)$ with an integral, a first step towards the upper bound on $c$ that, together with $b(p)\ge 1/p$, makes $a'(p)\le 0$.
--
--   **Formalization Note** The paper proves this by a chain of four steps (rewriting with $x_i=p^i$, the bound $(1-p)/\ln p\le -p$, a Riemann-sum comparison with $\int_0^p$, and dropping $\int_p^1$); only the first and last members of the chain are stated. The integrand is continuous and positive on $[0,1]$ (its denominator is at least $1/(ps)-1>0$; at $y=0$ Lean's `Real.log 0 = 0` gives the limit value), so the interval integral is the true integral. The series is a Lean `tsum` with the index shifted by one.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 36, B.9 (Proof of Theorem 9), the displayed chain for c(p), first and last members

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem b9_c_le_integral (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    cB9 s p ≤
      1 / p * (∫ y in (0 : ℝ)..1, 1 / (1 / (p * s) - 1 + y * (1 - p * Real.log y))) -
        s * (1 - p) := by sorry

end SampleDrivenOS.Linear
