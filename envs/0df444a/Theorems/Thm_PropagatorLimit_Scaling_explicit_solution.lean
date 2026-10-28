-- Prove2me | Theorems.Thm_PropagatorLimit_Scaling_explicit_solution
-- name    : PropagatorLimit.Scaling.explicit_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:09.592279+00:00
-- url     : https://prove2.me/theorems/51683c0b-7ac4-473c-a111-a258adbb9cc4
-- title:
--   Appendix A.1, p. 27 — explicit solution of the difference equation (2.1) under the scaling (3.1)
-- statement:
--   Let $\beta\in\mathbb R$, $T\ge0$, $N\in\mathbb N$, $g:\mathbb R\to\mathbb R$ and a process $F$ be given, with $\Delta t^N=T/N$ and increments $\Delta F^N_m=F_{t^N_m}-F_{t^N_{m-1}}$. Let $I^N$ be the discrete nonlinear propagator model
--   $$\Delta I^N_n=-\beta I^N_{n-1}\Delta t^N+\sqrt{\Delta t^N}\,g\Big(\tfrac{1}{\sqrt{\Delta t^N}}\Delta F^N_n\Big),\qquad I^N_0=0.$$
--   Then for every $n$ and every outcome
--   $$I^N_n=\sum_{m=1}^{n}\big(1-\beta\Delta t^N\big)^{n-m}\sqrt{\Delta t^N}\,g\Big(\tfrac{1}{\sqrt{\Delta t^N}}\Delta F^N_m\Big),$$
--   and, if $\beta\Delta t^N\ne1$,
--   $$I^N_n=\big(1-\beta\Delta t^N\big)^{n}\sqrt{\Delta t^N}\sum_{m=1}^{n}\big(1-\beta\Delta t^N\big)^{-m}g\Big(\tfrac{1}{\sqrt{\Delta t^N}}\Delta F^N_m\Big).$$
--
--   The second form writes $I^N_n$ as a discount factor times a sum of functions of the increments, which is the shape to which the functional central limit theorem (Theorem A.3) applies.
--
--   **Formalization Note** The identity is pathwise algebra and is stated for every $\beta$, $g$ and $F$, without the model's standing assumptions. The condition $\beta\Delta t^N\ne1$ (equivalently $\beta T\ne N$ when $N>0$) is **added** because the page writes the negative power $(1-\beta\Delta t^N)^{-m}$; for $N$ large it holds automatically.
-- source:
--   Muhle-Karbe, Wang & Webster, Stochastic liquidity as a proxy for nonlinear price impact, SSRN 4286108 (version of November 2, 2023), p. 27, Appendix A.1, explicit solution of the difference equation

import Mathlib
import Definitions.Def_PropagatorLimit_Scaling_Model

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace PropagatorLimit.Scaling

/-- Appendix A.1, p. 27: the explicit solution of the difference equation (2.1) under the
scaling (3.1), in both printed forms (the second needs `1 − βΔt^N ≠ 0`). -/
theorem explicit_solution {Ω : Type} (beta : ℝ) (T : ℝ≥0) (g : ℝ → ℝ) (F : ℝ≥0 → Ω → ℝ)
    (N n : ℕ) (ω : Ω) :
    INdisc beta T g F N n ω =
        ∑ m ∈ Finset.Icc 1 n, (1 - beta * dt T N) ^ (n - m) *
          (Real.sqrt (dt T N) * g (incr T N F m ω / Real.sqrt (dt T N))) ∧
      (beta * dt T N ≠ 1 →
        INdisc beta T g F N n ω =
          (1 - beta * dt T N) ^ n * Real.sqrt (dt T N) *
            ∑ m ∈ Finset.Icc 1 n, (1 - beta * dt T N) ^ (-(m : ℤ)) *
              g (incr T N F m ω / Real.sqrt (dt T N))) := by sorry

end PropagatorLimit.Scaling
