-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_b9_a_deriv_nonpos
-- name    : SampleDrivenOS.Linear.b9_a_deriv_nonpos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:31.168105+00:00
-- url     : https://prove2.me/theorems/8397847b-9b6c-4254-8da6-6f5d9ce7a2f9
-- title:
--   B.9, p. 37 — $\frac{d}{dp}a(p)\le 0$ on $(0,1)$
-- statement:
--   Let $\alpha^*\in(0,1)$ satisfy $\int_0^1 dy/(y(1-\ln y)+1/\alpha^*-1)=1$, suppose $\alpha^*\in[0.74,\,0.75]$, and let
--   $$a(p)=\sum_{i=1}^{\infty}\frac{\ln\bigl(\tfrac1p-\alpha^*(1-p^i(1+i(1-p)))\bigr)}{i(i+1)}+\alpha^*(2p-p^2).$$
--   Then for every $p\in(0,1)$ the function $a$ is differentiable at $p$ and
--   $$\frac{d}{dp}a(p)\le 0 .$$
--
--   Since $a(1)=\alpha^*$, this shows $a(p)\ge\alpha^*$ on $(0,1)$, which is the form of Theorem 9 obtained in the reduction.
--
--   **Formalization Note** The conclusion is stated as the existence of a derivative $d$ of $a$ at $p$ (`HasDerivAt`) with $d\le 0$, so that Lean's default value `deriv = 0` at a non-differentiable point cannot make it hold. The interval $[0.74,0.75]$ is how the paper uses "$\alpha^*\approx 0.745$"; see the previous milestone. The series is a Lean `tsum` with the index shifted by one.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 37, B.9 (Proof of Theorem 9), last display

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem b9_a_deriv_nonpos (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) (hs' : s ∈ Set.Icc (0.74 : ℝ) 0.75)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ d : ℝ, HasDerivAt (aB9 s) d p ∧ d ≤ 0 := by sorry

end SampleDrivenOS.Linear
