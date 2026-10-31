-- Prove2me | Theorems.Thm_RecursiveStopping_Infinite_gam_mem_A
-- name    : RecursiveStopping.Infinite.gam_mem_A
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:43:21.779737+00:00
-- url     : https://prove2.me/theorems/cb285d8a-7d8b-4ed1-8a78-b30002e8745b
-- title:
--   Proof of Theorem 3.1, (28) — $\Gamma$ maps $\mathcal A_d$ into itself
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb F,\mathsf P)$ satisfy the usual conditions, let $X$ be a right-continuous, strong Markov, quasi left-continuous flow on $\mathbb R^d$, let $r>0$, and assume Assumption 2.7 for $X$, $r$ and payoffs $\varphi,\psi$. Let $p\in(0,1)$ and let $\mu$ be the law of the delay.
--
--   For every $f\in\mathcal A_d$, $(\Gamma f)(x)<\infty$ for every $x\in\mathbb R^d$ and
--
--   $$
--   \Gamma f\in\mathcal A_d .
--   $$
--
--   Combined with the contraction estimate, this makes $\Gamma$ a self-map of the complete space $\mathcal A_d$, so Banach's fixed-point theorem applies.
--
--   Differences from the source:
--   - encoding: $\mathsf P_x$, $\mathsf E_x$ → the flow $X^x$ (or $Z^z$) under the single measure $\mathsf P$; reason: the paper defines $\mathsf E_x[f(X_\cdot)]=\mathsf E[f(X^x_\cdot)]$ (p.5)
--   - encoding: complete filtration → every set of $\mathsf P$-outer measure $0$ lies in $\mathcal F_0$; reason: the usual meaning of completeness
--   - encoding: $\tau\in\mathcal T$, payoff convention at $\tau=\infty$ → $\tau:\Omega\to[0,\infty]$ with `IsStoppingTime`, discounted payoff $0$ on $\{\tau=\infty\}$; reason: p.6 sets $f(X_\tau)1_{\{\tau=\infty\}}=\limsup_t f(X_t)$ and $e^{-r\tau}=0$ at $\tau=\infty$
--   - encoding: expectations and the integral against $F(\mathrm dt)$ in (3), (4), (12), (15) → `lintegral` of $[0,\infty]$-valued integrands; equation (3) as $\mathrm{ofReal}(v(x))=(\Gamma v)(x)$; reason: all integrands are non-negative, so the values coincide and no default value can enter
--   - encoding: strong Markov property for any integrable functional → for bounded measurable path functionals, on $\{\tau<\infty\}$; reason: equivalent by truncation and monotone convergence; $X_{\tau+\cdot}$ is only defined on $\{\tau<\infty\}$
--   - reading: the flow $x\mapsto X^x_t$ is P-a.s. continuous for all $t\ge0$ → for each $t$, P-a.s. continuous; reason: word order of p.8; the paper uses it at fixed $t$ (p.9, Lemma 3.3)
--   - encoding: a non-negative random variable $\vartheta$ independent of $X$ with distribution function $F$ → a probability measure $\mu$ on $[0,\infty)$ with $F(t)=\mu[0,t]$; reason: only the law of $\vartheta$ enters (4) and (12)
--   - encoding: $\mathbb R^d$ with no bound on $d$ → `EuclideanSpace ℝ (Fin d)` for every $d\in\mathbb N$ (and $m=d-1\in\mathbb N$ in the finite horizon); reason: the Euclidean norm is $|\cdot|_d$; the source states no bound on $d$
--   - encoding: $\Gamma f\in\mathcal A_d$ → $\Gamma f<\infty$ pointwise and its real part in $\mathcal A_d$; reason: $\Gamma f$ is $[0,\infty]$-valued in Lean
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, proof of Theorem 3.1, p.14, display (28)

import Mathlib
import Definitions.Def_RecursiveStopping_UsualConditions
import Definitions.Def_RecursiveStopping_MarkovFlow
import Definitions.Def_RecursiveStopping_Infinite_Assumption27
import Definitions.Def_RecursiveStopping_Infinite_Gam

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping.Infinite

/-- `Γ` maps `A_d` into itself (Colaneri & De Angelis, arXiv:1905.02650v4, proof of
Theorem 3.1, p.14, with display (28)): "First we prove that Γ maps `A_d` into itself. Fix
`f ∈ A_d` … Using (28) it is immediate to see that `∥(Γf)∥_{A_d} ≤ √c_0`, hence `Γf ∈ A_d`."

Under the standing assumptions of §2 (infinite horizon), for every `f ∈ A_d`, `(Γf)(x)` is
finite for every `x` and the real function `x ↦ (Γf)(x)` belongs to `A_d`. -/
theorem gam_mem_A {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ≥0 mΩ) (h𝔽 : UsualConditions P 𝔽)
    (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hX : MarkovFlow P 𝔽 X) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (r p : ℝ) (hr : 0 < r)
    (hp0 : 0 < p) (hp1 : p < 1) (ϕ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : Assumption27 P 𝔽 X r ϕ ψ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : InA f) :
    (∀ x, Gam P 𝔽 X μ r p ϕ ψ f x < ⊤) ∧ InA (fun x => (Gam P 𝔽 X μ r p ϕ ψ f x).toReal) := by sorry

end RecursiveStopping.Infinite
