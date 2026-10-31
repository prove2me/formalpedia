-- Prove2me | Theorems.Thm_RecursiveStopping_Infinite_display_11
-- name    : RecursiveStopping.Infinite.display_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:43:26.143536+00:00
-- url     : https://prove2.me/theorems/730e6771-0a2c-4f6f-b2de-003103c4c0ae
-- title:
--   Display (11) — $\lim_n\mathsf E[e^{-rt}|f(X^x_t)-f(X^{x_n}_t)|]=0$ for $f\in\mathcal A_d$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb F,\mathsf P)$ satisfy the usual conditions, let $X$ be a right-continuous, strong Markov, quasi left-continuous flow on $\mathbb R^d$, let $r>0$, and assume Assumption 2.7 for $X$, $r$ and payoffs $\varphi,\psi$.
--
--   For every $f\in\mathcal A_d$, every $t\ge0$ and every sequence $x_n\to x$ in $\mathbb R^d$,
--
--   $$
--   \lim_{n\to\infty}\mathsf E\Big[e^{-rt}\,\big|f(X^x_t)-f(X^{x_n}_t)\big|\Big]=0 .
--   $$
--
--   This continuity in $L^1$ of $x\mapsto f(X^x_t)$ is what makes $\Lambda f$ continuous in Lemma 3.2.
--
--   Differences from the source:
--   - encoding: $\mathsf P_x$, $\mathsf E_x$ → the flow $X^x$ (or $Z^z$) under the single measure $\mathsf P$; reason: the paper defines $\mathsf E_x[f(X_\cdot)]=\mathsf E[f(X^x_\cdot)]$ (p.5)
--   - encoding: complete filtration → every set of $\mathsf P$-outer measure $0$ lies in $\mathcal F_0$; reason: the usual meaning of completeness
--   - encoding: expectations and the integral against $F(\mathrm dt)$ in (3), (4), (12), (15) → `lintegral` of $[0,\infty]$-valued integrands; equation (3) as $\mathrm{ofReal}(v(x))=(\Gamma v)(x)$; reason: all integrands are non-negative, so the values coincide and no default value can enter
--   - encoding: strong Markov property for any integrable functional → for bounded measurable path functionals, on $\{\tau<\infty\}$; reason: equivalent by truncation and monotone convergence; $X_{\tau+\cdot}$ is only defined on $\{\tau<\infty\}$
--   - reading: the flow $x\mapsto X^x_t$ is P-a.s. continuous for all $t\ge0$ → for each $t$, P-a.s. continuous; reason: word order of p.8; the paper uses it at fixed $t$ (p.9, Lemma 3.3)
--   - encoding: $\mathbb R^d$ with no bound on $d$ → `EuclideanSpace ℝ (Fin d)` for every $d\in\mathbb N$ (and $m=d-1\in\mathbb N$ in the finite horizon); reason: the Euclidean norm is $|\cdot|_d$; the source states no bound on $d$
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, display (11), p.9

import Mathlib
import Definitions.Def_RecursiveStopping_UsualConditions
import Definitions.Def_RecursiveStopping_MarkovFlow
import Definitions.Def_RecursiveStopping_Infinite_Assumption27

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace RecursiveStopping.Infinite

/-- Display (11), Colaneri & De Angelis, arXiv:1905.02650v4, p.9: "by continuity of the flow
`x ↦ X^x_t` and of `f`, for any sequence `(x_n)_{n≥1}` converging to `x ∈ ℝ^d` and any `t ≥ 0`
… we also have `lim_{n→∞} E[e^{−rt}|f(X^x_t) − f(X^{x_n}_t)|] = 0`", for any `f ∈ A_d`.

Under the standing assumptions of §2: for every `f ∈ A_d`, every `t ≥ 0`, and every sequence
`x_n → x` in `ℝ^d`, `E[e^{−rt}|f(X^x_t) − f(X^{x_n}_t)|] → 0`. -/
theorem display_11 {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ≥0 mΩ) (h𝔽 : UsualConditions P 𝔽)
    (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hX : MarkovFlow P 𝔽 X) (r : ℝ) (hr : 0 < r) (ϕ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : Assumption27 P 𝔽 X r ϕ ψ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : InA f)
    (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin d)) (xs : ℕ → EuclideanSpace ℝ (Fin d))
    (hxs : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun n => ∫⁻ ω,
      ENNReal.ofReal (Real.exp (-r * (t : ℝ)) * |f (X x t ω) - f (X (xs n) t ω)|) ∂P)
      atTop (𝓝 0) := by sorry

end RecursiveStopping.Infinite
