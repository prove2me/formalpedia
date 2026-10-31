-- Prove2me | Theorems.Thm_RecursiveStopping_lemma_3_2
-- name    : RecursiveStopping.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:44:24.458556+00:00
-- url     : https://prove2.me/theorems/872ad87f-2bbf-43c4-a016-6c8bf109aff5
-- title:
--   Lemma 3.2 — $\Lambda$ maps $\mathcal A_d$ into itself (both horizons)
-- statement:
--   **Standing assumptions.** $(\Omega,\mathcal F,\mathbb F,\mathsf P)$ satisfies the usual conditions (right-continuous complete filtration, $\mathcal F_\infty=\mathcal F$); $\mu$ is the law of the delay $\vartheta$ on $[0,\infty)$; $r>0$ and $p\in(0,1)$.
--
--   - *Infinite horizon:* $X$ is a right-continuous, strong Markov, quasi left-continuous flow on $\mathbb R^d$ satisfying Assumption 2.7 with payoffs $\varphi\le\psi$ in $\mathcal A_d$.
--   - *Finite horizon:* $T\ge0$, $Z$ is a right-continuous, strong Markov, quasi left-continuous space-time flow on $\mathbb R\times\mathbb R^{d-1}$ satisfying Assumption 2.7 in its finite-horizon reading and Assumption 2.8.
--
--   1. *Infinite horizon.* For every $f\in\mathcal A_d$, $(\Lambda f)(x)<\infty$ for every $x$ and $\Lambda f\in\mathcal A_d$, with $\Lambda$ as in (4).
--   2. *Finite horizon.* For every $f$ in the finite-horizon $\mathcal A_d$, $(\Lambda f)(z)<\infty$ for every $z\in[0,T]\times\mathbb R^{d-1}$ and $\Lambda f$, defined by (12), belongs to the finite-horizon $\mathcal A_d$.
--
--   This is the first step of the contraction argument: the delayed-option operator preserves continuity, non-negativity and linear growth.
--
--   Differences from the source:
--   - encoding: $\mathsf P_x$, $\mathsf E_x$ → the flow $X^x$ (or $Z^z$) under the single measure $\mathsf P$; reason: the paper defines $\mathsf E_x[f(X_\cdot)]=\mathsf E[f(X^x_\cdot)]$ (p.5)
--   - encoding: complete filtration → every set of $\mathsf P$-outer measure $0$ lies in $\mathcal F_0$; reason: the usual meaning of completeness
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
--   - encoding: $\Lambda f\in\mathcal A_d$ → $\Lambda f<\infty$ pointwise and $x\mapsto(\Lambda f)(x)$ (real part) in $\mathcal A_d$; reason: $\Lambda f$ is $[0,\infty]$-valued in Lean; finiteness makes the real function exact
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, Lemma 3.2, p.11 (finite horizon: proof of Lemma 3.2, p.11, and §3, p.10)

import Mathlib
import Definitions.Def_RecursiveStopping_UsualConditions
import Definitions.Def_RecursiveStopping_MarkovFlow
import Definitions.Def_RecursiveStopping_Infinite_Assumption27
import Definitions.Def_RecursiveStopping_Finite_Assumption27
import Definitions.Def_RecursiveStopping_Finite_Assumption28
import Definitions.Def_RecursiveStopping_Infinite_Lam
import Definitions.Def_RecursiveStopping_Finite_Lam

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping

/-- Lemma 3.2, Colaneri & De Angelis, arXiv:1905.02650v4, p.11: "For every `f ∈ A_d` it holds
that `Λf ∈ A_d`." (Proof: "The proof is identical in the finite-time horizon case, where we use
`Λf` as in (12).")

Standing assumptions (both horizons): a probability space `(Ω, F, P)` with a filtration `𝔽`
satisfying the usual conditions of p.5, a delay law `μ` (a probability measure on `[0, ∞)`,
`F(t) = μ[0, t]`), `r > 0`, `p ∈ (0, 1)`. Infinite horizon: a flow `X` on `ℝ^d` with the process
axioms of p.5 and Assumption 2.7. Finite horizon (§2.2): `T ≥ 0`, a space-time flow `Z` on
`ℝ × ℝ^{d−1}` with the process axioms, Assumption 2.7 in the reading of pp.9–10, and
Assumption 2.8.

Infinite horizon: for every `f ∈ A_d`, `(Λf)(x) < ∞` for every `x` and `x ↦ (Λf)(x)` belongs to
`A_d`. Finite horizon: for every `f ∈ A_d` (on `[0, T] × ℝ^{d−1}`), `(Λf)(z) < ∞` on
`[0, T] × ℝ^{d−1}` and `Λf` (from (12)) belongs to `A_d`. -/
theorem lemma_3_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (h𝔽 : UsualConditions P 𝔽) (μ : Measure ℝ≥0)
    [IsProbabilityMeasure μ] (r p : ℝ) (hr : 0 < r) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ (d : ℕ) (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      MarkovFlow P 𝔽 X → ∀ ϕ ψ : EuclideanSpace ℝ (Fin d) → ℝ, Infinite.Assumption27 P 𝔽 X r ϕ ψ →
      ∀ f, Infinite.InA f →
        (∀ x, Infinite.Lam P X μ r p ψ f x < ⊤) ∧
        Infinite.InA (fun x => (Infinite.Lam P X μ r p ψ f x).toReal)) ∧
    (∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      ∀ Z : ℝ × EuclideanSpace ℝ (Fin m) → ℝ≥0 → Ω → ℝ × EuclideanSpace ℝ (Fin m),
      MarkovFlow P 𝔽 Z → ∀ ϕ ψ : ℝ × EuclideanSpace ℝ (Fin m) → ℝ,
      Finite.Assumption27 P 𝔽 Z T r ϕ ψ → Finite.Assumption28 μ T →
      ∀ f, Finite.InA T f →
        (∀ z ∈ Finite.Dom m T, Finite.Lam P Z μ T r p ψ f z < ⊤) ∧
        Finite.InA T (fun z => (Finite.Lam P Z μ T r p ψ f z).toReal)) := by sorry

end RecursiveStopping
