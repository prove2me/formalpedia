-- Prove2me | Theorems.Thm_RecursiveStopping_Infinite_display_9
-- name    : RecursiveStopping.Infinite.display_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:43:18.71401+00:00
-- url     : https://prove2.me/theorems/bb32663a-dfb0-4328-9c88-54347ba837ae
-- title:
--   Display (9) — optional sampling for $\widehat X$: $\mathsf E_x[\widehat X_\tau]\le 1+|x|_d^2$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb F,\mathsf P)$ satisfy the usual conditions, let $X$ be a right-continuous, strong Markov, quasi left-continuous flow on $\mathbb R^d$, let $r>0$, and assume Assumption 2.7 for $X$, $r$ and payoffs $\varphi,\psi$.
--
--   Let $\rho\in(0,1)$ be such that, for every $x$,
--   $$\widehat X_t=e^{-2r(1-\rho)t}\big(1+|X^x_t|_d^2\big)$$
--   is an $\mathbb F$-supermartingale, as in Assumption 2.7 (i). Then for every $x\in\mathbb R^d$ and every $\mathbb F$-stopping time $\tau$ with values in $[0,\infty]$,
--
--   $$
--   \mathsf E\big[\widehat X_\tau\big]\le 1+|x|_d^2,
--   $$
--
--   where on $\{\tau=\infty\}$ the value $\widehat X_\infty$ is $\limsup_{t\to\infty}\widehat X_t$, the almost-sure limit of the non-negative supermartingale.
--
--   This bound is used throughout §3 to control $e^{-2r\tau}(1+|X_\tau|^2)$ uniformly over stopping times, in particular in (24), (28), (29) and (33).
--
--   **Formalization Note** The expectation is a Lebesgue integral of a $[0,\infty]$-valued function over all of $\Omega$, including $\{\tau=\infty\}$.
--
--   Differences from the source:
--   - encoding: $\mathsf P_x$, $\mathsf E_x$ → the flow $X^x$ (or $Z^z$) under the single measure $\mathsf P$; reason: the paper defines $\mathsf E_x[f(X_\cdot)]=\mathsf E[f(X^x_\cdot)]$ (p.5)
--   - encoding: complete filtration → every set of $\mathsf P$-outer measure $0$ lies in $\mathcal F_0$; reason: the usual meaning of completeness
--   - encoding: $\widehat X_\infty$ (supermartingale for $t\in[0,\infty]$) → $\limsup_{t\to\infty}\widehat X_t$ in $[0,\infty]$; reason: a non-negative supermartingale converges a.s., so $\limsup$ is its a.s. limit
--   - encoding: $\rho$ of Assumption 2.7 (i) → any $\rho\in(0,1)$ for which the supermartingale property holds, on top of Assumption 2.7; reason: (9) is stated for the process of (i); quantifying over every admissible $\rho$ includes it
--   - encoding: $\tau\in\mathcal T$, payoff convention at $\tau=\infty$ → $\tau:\Omega\to[0,\infty]$ with `IsStoppingTime`, discounted payoff $0$ on $\{\tau=\infty\}$; reason: p.6 sets $f(X_\tau)1_{\{\tau=\infty\}}=\limsup_t f(X_t)$ and $e^{-r\tau}=0$ at $\tau=\infty$
--   - encoding: strong Markov property for any integrable functional → for bounded measurable path functionals, on $\{\tau<\infty\}$; reason: equivalent by truncation and monotone convergence; $X_{\tau+\cdot}$ is only defined on $\{\tau<\infty\}$
--   - reading: the flow $x\mapsto X^x_t$ is P-a.s. continuous for all $t\ge0$ → for each $t$, P-a.s. continuous; reason: word order of p.8; the paper uses it at fixed $t$ (p.9, Lemma 3.3)
--   - encoding: $\mathbb R^d$ with no bound on $d$ → `EuclideanSpace ℝ (Fin d)` for every $d\in\mathbb N$ (and $m=d-1\in\mathbb N$ in the finite horizon); reason: the Euclidean norm is $|\cdot|_d$; the source states no bound on $d$
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, display (9), p.9

import Mathlib
import Definitions.Def_RecursiveStopping_UsualConditions
import Definitions.Def_RecursiveStopping_MarkovFlow
import Definitions.Def_RecursiveStopping_Infinite_Assumption27

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace RecursiveStopping.Infinite

/-- Display (9), Colaneri & De Angelis, arXiv:1905.02650v4, p.9: "since the process `X̂` in (i)
of Assumption 2.7 is a non-negative supermartingale, then it is a supermartingale for
`t ∈ [0, ∞]` and the optional sampling theorem gives `E_x[X̂_τ] ≤ (1 + |x|_d²)`, for any
`τ ∈ 𝒯` and `x ∈ ℝ^d`."

Under the standing assumptions of §2 (usual conditions, the process axioms, Assumption 2.7),
for every `ρ ∈ (0, 1)` such that `X̂_t = e^{−2r(1−ρ)t}(1 + |X^x_t|_d²)` is an `𝔽`-supermartingale
for every `x`, every `x` and every `𝔽`-stopping time `τ` with values in `[0, ∞]`:
`E[X̂_τ] ≤ 1 + |x|_d²`.

**Formalization Note** On `{τ = ∞}`, `X̂_∞` is `lim sup_{t→∞} X̂_t` (the a.s. limit of the
non-negative supermartingale `X̂`); the expectation is a `lintegral` over all of `Ω`. -/
theorem display_9 {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ≥0 mΩ) (h𝔽 : UsualConditions P 𝔽)
    (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hX : MarkovFlow P 𝔽 X) (r : ℝ) (hr : 0 < r) (ϕ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : Assumption27 P 𝔽 X r ϕ ψ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρ : ∀ x, Supermartingale
      (fun (t : ℝ≥0) ω => Real.exp (-2 * r * (1 - ρ) * (t : ℝ)) * (1 + ‖X x t ω‖ ^ 2)) 𝔽 P)
    (x : EuclideanSpace ℝ (Fin d)) (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝔽 τ) :
    ∫⁻ ω, (if τ ω = ⊤ then
        limsup (fun t : ℝ≥0 =>
          ENNReal.ofReal (Real.exp (-2 * r * (1 - ρ) * (t : ℝ)) * (1 + ‖X x t ω‖ ^ 2))) atTop
      else ENNReal.ofReal (Real.exp (-2 * r * (1 - ρ) * (τ ω).toReal) *
        (1 + ‖X x (τ ω).toNNReal ω‖ ^ 2))) ∂P
      ≤ ENNReal.ofReal (1 + ‖x‖ ^ 2) := by sorry

end RecursiveStopping.Infinite
