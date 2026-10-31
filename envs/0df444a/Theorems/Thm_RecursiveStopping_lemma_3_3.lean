-- Prove2me | Theorems.Thm_RecursiveStopping_lemma_3_3
-- name    : RecursiveStopping.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:44:51.804593+00:00
-- url     : https://prove2.me/theorems/7d96d9e9-c47b-42d9-ade1-872758d9325d
-- title:
--   Lemma 3.3 — optimal stopping time, lower semicontinuity and (super)martingales for $\Gamma f$ (both horizons)
-- statement:
--   **Standing assumptions.** $(\Omega,\mathcal F,\mathbb F,\mathsf P)$ satisfies the usual conditions (right-continuous complete filtration, $\mathcal F_\infty=\mathcal F$); $\mu$ is the law of the delay $\vartheta$ on $[0,\infty)$; $r>0$ and $p\in(0,1)$.
--
--   - *Infinite horizon:* $X$ is a right-continuous, strong Markov, quasi left-continuous flow on $\mathbb R^d$ satisfying Assumption 2.7 with payoffs $\varphi\le\psi$ in $\mathcal A_d$.
--   - *Finite horizon:* $T\ge0$, $Z$ is a right-continuous, strong Markov, quasi left-continuous space-time flow on $\mathbb R\times\mathbb R^{d-1}$ satisfying Assumption 2.7 in its finite-horizon reading and Assumption 2.8.
--
--   *Infinite horizon.* For every $f\in\mathcal A_d$, with $G=\max\{\varphi,\Lambda f\}$:
--
--   1. $\Gamma f$ is finite and lower semicontinuous on $\mathbb R^d$;
--   2. for every $x$, the time
--   $$\tau^f_*=\inf\{s\ge0:(\Gamma f)(X^x_s)=\max[\varphi(X^x_s),(\Lambda f)(X^x_s)]\}$$
--   is an $\mathbb F$-stopping time and is optimal: $\mathsf E\big[e^{-r\tau^f_*}G(X^x_{\tau^f_*})\big]=(\Gamma f)(x)$ (payoff $0$ on $\{\tau^f_*=\infty\}$);
--   3. $t\mapsto e^{-rt}(\Gamma f)(X^x_t)$, $t\in[0,\infty]$, is an $\mathbb F$-supermartingale (value $0$ at $t=\infty$) with right-continuous non-negative paths;
--   4. $t\mapsto e^{-r(t\wedge\tau^f_*)}(\Gamma f)(X^x_{t\wedge\tau^f_*})$, $t\in[0,\infty)$, is an $\mathbb F$-martingale with right-continuous non-negative paths.
--
--   *Finite horizon.* For every $f$ in the finite-horizon $\mathcal A_d$ and every $z=(t,x)\in[0,T]\times\mathbb R^{d-1}$: $\Gamma f$ is finite on $[0,T]\times\mathbb R^{d-1}$ and lower semicontinuous relative to it; $\tau^f_*$, with the infimum over $s\in[0,T-t]$, is a stopping time with $\tau^f_*\le T-t$ a.s. and is optimal; the two processes, indexed by $s\in[0,T-t]$, are a supermartingale and a martingale with right-continuous non-negative paths.
--
--   This is the well-posedness of the stopping problem (15) for a fixed continuation value $f$.
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
--   - encoding: supermartingale for $t\in[0,\infty]$ → `IsClosedSupermartingale`: index $[0,\infty]$, filtration with $\mathcal F_\infty=\bigvee_t\mathcal F_t$, value $0$ at $\infty$; reason: the p.6 convention gives $e^{-r\cdot\infty}\limsup_t v(X_t)=0$ at $t=\infty$
--   - encoding: right-continuous (non-negative) process → every path right-continuous and every value non-negative; reason: the literal reading of a right-continuous non-negative process
--   - reading: finite horizon: Assumption 2.7 'understood to hold for $t\in[0,T]$', (i) for the spatial part (pp.9–10) → space-time flow $Z^{(t,x)}_s=(t+s,X_s)$ defined for every start and all $s\ge0$ with the process axioms; flow continuity on $[0,T]\times\mathbb R^{d-1}$; (i) for the spatial part and (ii)–(iii) with $\sup_{s\ge0}$, for starting points in $[0,T]\times\mathbb R^{d-1}$; reason: the source specifies the finite-horizon set-up only by this sentence; the proof of Lemma 3.4, Step 2 (p.14), uses the flow after $T-t$
--   - encoding: $|\cdot|_d$ on $\mathbb R^d=\mathbb R\times\mathbb R^{d-1}$ in (ii)–(iii), finite horizon → the product (max) norm on $\mathbb R\times\mathbb R^{d-1}$; reason: equivalent norms; finiteness in (ii) and the limit $0$ in (iii) are unchanged
--   - reading: (12) prints $e^{-rt}$ inside $\int_0^{T-t}\cdots F(\mathrm ds)$ → $e^{-rs}$; reason: the page reuses $t$, the fixed time coordinate of $z$, under the integral in $s$; (12) comes from Problem 1' (p.9), whose discount is $e^{-r(\tau+\vartheta)}$, so the factor is $e^{-rs}$ as in (4); this changes the operator, so it is a reading, not an encoding
--   - encoding: Assumption 2.8: $F$ continuous on $[0,T]$, $F(0)$ possibly positive → $\mu(\{s\})=0$ for $s\in(0,T]$; reason: a distribution function is right-continuous, so continuity on $[0,T]$ is the absence of atoms in $(0,T]$
--   - encoding: a fixed horizon $T<\infty$ → $T\in\mathbb R$ with $0\le T$; reason: the horizon of the interval $[0,T]$
--   - encoding: finite horizon: the processes for $s\in[0,T-t]$ → processes on $s\ge0$ frozen at $s=T-t$ (the stopped one at $s\wedge\tau_*\wedge(T-t)$); reason: same process on $[0,T-t]$; $\tau_*\le T-t$ a.s., so the extra cap changes nothing a.s.
--   - encoding: $\Gamma f$ as a real function, lower semicontinuous → $\Gamma f$ is $[0,\infty]$-valued; finiteness is stated, lower semicontinuity is in $[0,\infty]$, and the processes use its real part; reason: finite values make the two readings equal
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, Lemma 3.3, p.11 (finite horizon: §3, p.10, and the remark on T < ∞, p.11)

import Mathlib
import Definitions.Def_RecursiveStopping_UsualConditions
import Definitions.Def_RecursiveStopping_MarkovFlow
import Definitions.Def_RecursiveStopping_Infinite_Assumption27
import Definitions.Def_RecursiveStopping_Finite_Assumption27
import Definitions.Def_RecursiveStopping_Finite_Assumption28
import Definitions.Def_RecursiveStopping_Infinite_Gam
import Definitions.Def_RecursiveStopping_Finite_Gam
import Definitions.Def_RecursiveStopping_entryTime
import Definitions.Def_RecursiveStopping_IsClosedSupermartingale

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping

/-- Lemma 3.3, Colaneri & De Angelis, arXiv:1905.02650v4, p.11: "For every `f ∈ A_d`, the
stopping problem in (15) is well-posed in the sense that
`τ^f_* = inf{s ≥ 0 : (Γf)(X_s) = max[ϕ(X_s), (Λf)(X_s)]}` (17) is an optimal stopping time, the
function `Γf` is lower semi-continuous, the process `t ↦ e^{−rt}(Γf)(X_t)`, `t ∈ [0, ∞]` (18) is
a right-continuous (non-negative), `P_x`-supermartingale and the stopped process
`t ↦ e^{−r(t∧τ^f_*)}(Γf)(X_{t∧τ^f_*})`, `t ∈ [0, ∞)` (19) is a right-continuous (non-negative),
`P_x`-martingale, for any `x ∈ ℝ^d`." §3 (p.10) states all results for both horizons; in the
finite horizon "the infimum in (16) is taken on `s ∈ [0, T − t]` … The same comment applies to
(17)" (p.11).

Standing assumptions (both horizons): a probability space `(Ω, F, P)` with a filtration `𝔽`
satisfying the usual conditions of p.5, a delay law `μ` (a probability measure on `[0, ∞)`,
`F(t) = μ[0, t]`), `r > 0`, `p ∈ (0, 1)`. Infinite horizon: a flow `X` on `ℝ^d` with the process
axioms of p.5 and Assumption 2.7. Finite horizon (§2.2): `T ≥ 0`, a space-time flow `Z` on
`ℝ × ℝ^{d−1}` with the process axioms, Assumption 2.7 in the reading of pp.9–10, and
Assumption 2.8.

Infinite horizon, for every `f ∈ A_d`, with `G = max{ϕ, Λf}`:
1. `Γf` is finite and lower semicontinuous;
2. for every `x`, `τ^f_*` (the entry time of `{Γf = G}`) is an `𝔽`-stopping time and
   `E[e^{−rτ^f_*}G(X^x_{τ^f_*})] = (Γf)(x)` (payoff `0` on `{τ^f_* = ∞}`);
3. `t ↦ e^{−rt}(Γf)(X^x_t)` is an `𝔽`-supermartingale on `[0, ∞]` (value `0` at `∞`) with
   right-continuous, non-negative paths;
4. `t ↦ e^{−r(t∧τ^f_*)}(Γf)(X^x_{t∧τ^f_*})` is an `𝔽`-martingale on `[0, ∞)` with
   right-continuous, non-negative paths.

Finite horizon, for every `f ∈ A_d` and `z = (t, x) ∈ [0, T] × ℝ^{d−1}`: the same, with
`τ^f_*` the entry time before `T − t` (an admissible stopping time, `≤ T − t` a.s.), lower
semicontinuity relative to `[0, T] × ℝ^{d−1}`, and both processes indexed by `s ∈ [0, T − t]`,
i.e. frozen at time `T − t`.

**Formalization Note** `Γf` is `[0, ∞]`-valued; the processes use `(Γf)(·).toReal`, which is
exact by clause 1. -/
theorem lemma_3_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (h𝔽 : UsualConditions P 𝔽) (μ : Measure ℝ≥0)
    [IsProbabilityMeasure μ] (r p : ℝ) (hr : 0 < r) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ (d : ℕ) (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      MarkovFlow P 𝔽 X → ∀ ϕ ψ : EuclideanSpace ℝ (Fin d) → ℝ, Infinite.Assumption27 P 𝔽 X r ϕ ψ →
      ∀ f, Infinite.InA f →
        let Γf := Infinite.Gam P 𝔽 X μ r p ϕ ψ f
        let G := fun y => max (ENNReal.ofReal (ϕ y)) (Infinite.Lam P X μ r p ψ f y)
        (∀ x, Γf x < ⊤) ∧ LowerSemicontinuous Γf ∧
        ∀ x,
          let τf := entryTime X x {y | Γf y = G y} ⊤
          let Y : ℝ≥0 → Ω → ℝ := fun t ω => Real.exp (-r * (t : ℝ)) * (Γf (X x t ω)).toReal
          let Ys : ℝ≥0 → Ω → ℝ := fun t ω =>
            Real.exp (-r * (min (t : ℝ≥0∞) (τf ω)).toReal) *
              (Γf (X x (min (t : ℝ≥0∞) (τf ω)).toNNReal ω)).toReal
          IsStoppingTime 𝔽 τf ∧
          ∫⁻ ω, discPayoff r G X x τf ω ∂P = Γf x ∧
          IsClosedSupermartingale P 𝔽 Y ∧
          (∀ ω (t : ℝ≥0), ContinuousWithinAt (fun s => Y s ω) (Set.Ici t) t) ∧
          (∀ t ω, 0 ≤ Y t ω) ∧
          Martingale Ys 𝔽 P ∧
          (∀ ω (t : ℝ≥0), ContinuousWithinAt (fun s => Ys s ω) (Set.Ici t) t) ∧
          (∀ t ω, 0 ≤ Ys t ω)) ∧
    (∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      ∀ Z : ℝ × EuclideanSpace ℝ (Fin m) → ℝ≥0 → Ω → ℝ × EuclideanSpace ℝ (Fin m),
      MarkovFlow P 𝔽 Z → ∀ ϕ ψ : ℝ × EuclideanSpace ℝ (Fin m) → ℝ,
      Finite.Assumption27 P 𝔽 Z T r ϕ ψ → Finite.Assumption28 μ T →
      ∀ f, Finite.InA T f →
        let Γf := Finite.Gam P 𝔽 Z μ T r p ϕ ψ f
        let G := fun y => max (ENNReal.ofReal (ϕ y)) (Finite.Lam P Z μ T r p ψ f y)
        (∀ z ∈ Finite.Dom m T, Γf z < ⊤) ∧ LowerSemicontinuousOn Γf (Finite.Dom m T) ∧
        ∀ z ∈ Finite.Dom m T,
          let c : ℝ≥0∞ := ENNReal.ofReal (T - z.1)
          let τf := entryTime Z z {y | Γf y = G y} c
          let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
            Real.exp (-r * (min (s : ℝ≥0∞) c).toReal) * (Γf (Z z (min (s : ℝ≥0∞) c).toNNReal ω)).toReal
          let Ys : ℝ≥0 → Ω → ℝ := fun s ω =>
            Real.exp (-r * (min (min (s : ℝ≥0∞) (τf ω)) c).toReal) *
              (Γf (Z z (min (min (s : ℝ≥0∞) (τf ω)) c).toNNReal ω)).toReal
          IsStoppingTime 𝔽 τf ∧ (∀ᵐ ω ∂P, τf ω ≤ c) ∧
          ∫⁻ ω, discPayoff r G Z z τf ω ∂P = Γf z ∧
          Supermartingale Y 𝔽 P ∧
          (∀ ω (s : ℝ≥0), ContinuousWithinAt (fun u => Y u ω) (Set.Ici s) s) ∧
          (∀ s ω, 0 ≤ Y s ω) ∧
          Martingale Ys 𝔽 P ∧
          (∀ ω (s : ℝ≥0), ContinuousWithinAt (fun u => Ys u ω) (Set.Ici s) s) ∧
          (∀ s ω, 0 ≤ Ys s ω)) := by sorry

end RecursiveStopping
