-- Prove2me | Theorems.Thm_RecursiveStopping_lemma_3_4
-- name    : RecursiveStopping.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:44:24.57999+00:00
-- url     : https://prove2.me/theorems/a97e8189-eab4-45c6-b06a-aa57803e93ec
-- title:
--   Lemma 3.4 — $\Gamma f$ is upper semicontinuous (both horizons)
-- statement:
--   **Standing assumptions.** $(\Omega,\mathcal F,\mathbb F,\mathsf P)$ satisfies the usual conditions (right-continuous complete filtration, $\mathcal F_\infty=\mathcal F$); $\mu$ is the law of the delay $\vartheta$ on $[0,\infty)$; $r>0$ and $p\in(0,1)$.
--
--   - *Infinite horizon:* $X$ is a right-continuous, strong Markov, quasi left-continuous flow on $\mathbb R^d$ satisfying Assumption 2.7 with payoffs $\varphi\le\psi$ in $\mathcal A_d$.
--   - *Finite horizon:* $T\ge0$, $Z$ is a right-continuous, strong Markov, quasi left-continuous space-time flow on $\mathbb R\times\mathbb R^{d-1}$ satisfying Assumption 2.7 in its finite-horizon reading and Assumption 2.8.
--
--   1. *Infinite horizon.* For every $f\in\mathcal A_d$, every $x\in\mathbb R^d$ and every sequence $x_n\to x$,
--   $$\limsup_{n\to\infty}(\Gamma f)(x_n)\le(\Gamma f)(x).$$
--   2. *Finite horizon.* For every $f$ in the finite-horizon $\mathcal A_d$, the same holds for every $z\in[0,T]\times\mathbb R^{d-1}$ and every sequence $z_n\to z$ inside $[0,T]\times\mathbb R^{d-1}$.
--
--   Together with Lemma 3.3 this makes $\Gamma f$ continuous, which is needed for $\Gamma f\in\mathcal A_d$.
--
--   **Formalization Note** Stated as upper semicontinuity of the $[0,\infty]$-valued $\Gamma f$ (relative to $[0,T]\times\mathbb R^{d-1}$ in the finite horizon), which on a metric space is the sequential condition (22).
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
--   - reading: finite horizon: Assumption 2.7 'understood to hold for $t\in[0,T]$', (i) for the spatial part (pp.9–10) → space-time flow $Z^{(t,x)}_s=(t+s,X_s)$ defined for every start and all $s\ge0$ with the process axioms; flow continuity on $[0,T]\times\mathbb R^{d-1}$; (i) for the spatial part and (ii)–(iii) with $\sup_{s\ge0}$, for starting points in $[0,T]\times\mathbb R^{d-1}$; reason: the source specifies the finite-horizon set-up only by this sentence; the proof of Lemma 3.4, Step 2 (p.14), uses the flow after $T-t$
--   - encoding: $|\cdot|_d$ on $\mathbb R^d=\mathbb R\times\mathbb R^{d-1}$ in (ii)–(iii), finite horizon → the product (max) norm on $\mathbb R\times\mathbb R^{d-1}$; reason: equivalent norms; finiteness in (ii) and the limit $0$ in (iii) are unchanged
--   - reading: (12) prints $e^{-rt}$ inside $\int_0^{T-t}\cdots F(\mathrm ds)$ → $e^{-rs}$; reason: the page reuses $t$, the fixed time coordinate of $z$, under the integral in $s$; (12) comes from Problem 1' (p.9), whose discount is $e^{-r(\tau+\vartheta)}$, so the factor is $e^{-rs}$ as in (4); this changes the operator, so it is a reading, not an encoding
--   - encoding: Assumption 2.8: $F$ continuous on $[0,T]$, $F(0)$ possibly positive → $\mu(\{s\})=0$ for $s\in(0,T]$; reason: a distribution function is right-continuous, so continuity on $[0,T]$ is the absence of atoms in $(0,T]$
--   - encoding: a fixed horizon $T<\infty$ → $T\in\mathbb R$ with $0\le T$; reason: the horizon of the interval $[0,T]$
--   - encoding: (22) for every sequence $x_n\to x$ → `UpperSemicontinuous` (finite horizon: `UpperSemicontinuousOn` the domain) of the $[0,\infty]$-valued $\Gamma f$; reason: sequential and topological upper semicontinuity agree on metric spaces; $\Gamma f$ is finite by Lemma 3.3
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, Lemma 3.4, p.12 (Step 2, finite horizon, pp.13–14)

import Mathlib
import Definitions.Def_RecursiveStopping_UsualConditions
import Definitions.Def_RecursiveStopping_MarkovFlow
import Definitions.Def_RecursiveStopping_Infinite_Assumption27
import Definitions.Def_RecursiveStopping_Finite_Assumption27
import Definitions.Def_RecursiveStopping_Finite_Assumption28
import Definitions.Def_RecursiveStopping_Infinite_Gam
import Definitions.Def_RecursiveStopping_Finite_Gam

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping

/-- Lemma 3.4, Colaneri & De Angelis, arXiv:1905.02650v4, p.12: "For every `f ∈ A_d` and
`x ∈ ℝ^d` given and fixed, we have `lim sup_{n→∞} (Γf)(x_n) ≤ (Γf)(x)` for any sequence
`(x_n)_{n≥1}` such that `x_n → x` as `n → ∞`." The proof treats the infinite horizon (Step 1)
and the finite horizon (Step 2, sequences `z_n → z` in `[0, T] × ℝ^{d−1}`).

Standing assumptions (both horizons): a probability space `(Ω, F, P)` with a filtration `𝔽`
satisfying the usual conditions of p.5, a delay law `μ` (a probability measure on `[0, ∞)`,
`F(t) = μ[0, t]`), `r > 0`, `p ∈ (0, 1)`. Infinite horizon: a flow `X` on `ℝ^d` with the process
axioms of p.5 and Assumption 2.7. Finite horizon (§2.2): `T ≥ 0`, a space-time flow `Z` on
`ℝ × ℝ^{d−1}` with the process axioms, Assumption 2.7 in the reading of pp.9–10, and
Assumption 2.8.

Conclusion: for every `f ∈ A_d`, `Γf` is upper semicontinuous on `ℝ^d` (infinite horizon), and
upper semicontinuous on `[0, T] × ℝ^{d−1}` relative to that set (finite horizon).

**Formalization Note** `Γf` is `[0, ∞]`-valued; on a metric space upper semicontinuity is the
sequential condition (22). -/
theorem lemma_3_4 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (h𝔽 : UsualConditions P 𝔽) (μ : Measure ℝ≥0)
    [IsProbabilityMeasure μ] (r p : ℝ) (hr : 0 < r) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ (d : ℕ) (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      MarkovFlow P 𝔽 X → ∀ ϕ ψ : EuclideanSpace ℝ (Fin d) → ℝ, Infinite.Assumption27 P 𝔽 X r ϕ ψ →
      ∀ f, Infinite.InA f → UpperSemicontinuous (Infinite.Gam P 𝔽 X μ r p ϕ ψ f)) ∧
    (∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      ∀ Z : ℝ × EuclideanSpace ℝ (Fin m) → ℝ≥0 → Ω → ℝ × EuclideanSpace ℝ (Fin m),
      MarkovFlow P 𝔽 Z → ∀ ϕ ψ : ℝ × EuclideanSpace ℝ (Fin m) → ℝ,
      Finite.Assumption27 P 𝔽 Z T r ϕ ψ → Finite.Assumption28 μ T →
      ∀ f, Finite.InA T f →
        UpperSemicontinuousOn (Finite.Gam P 𝔽 Z μ T r p ϕ ψ f) (Finite.Dom m T)) := by sorry

end RecursiveStopping
