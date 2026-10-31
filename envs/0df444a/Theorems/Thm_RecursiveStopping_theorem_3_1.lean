-- Prove2me | Theorems.Thm_RecursiveStopping_theorem_3_1
-- name    : RecursiveStopping.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:44:40.936097+00:00
-- url     : https://prove2.me/theorems/a40fbe09-3ed0-41f4-af98-b4c8c2dab7ad
-- title:
--   Theorem 3.1 — the recursive value is the unique fixed point in $\mathcal A_d$ and the first contact time is optimal (both horizons)
-- statement:
--   **Standing assumptions.** $(\Omega,\mathcal F,\mathbb F,\mathsf P)$ satisfies the usual conditions (right-continuous complete filtration, $\mathcal F_\infty=\mathcal F$); $\mu$ is the law of the delay $\vartheta$ on $[0,\infty)$; $r>0$ and $p\in(0,1)$.
--
--   - *Infinite horizon:* $X$ is a right-continuous, strong Markov, quasi left-continuous flow on $\mathbb R^d$ satisfying Assumption 2.7 with payoffs $\varphi\le\psi$ in $\mathcal A_d$.
--   - *Finite horizon:* $T\ge0$, $Z$ is a right-continuous, strong Markov, quasi left-continuous space-time flow on $\mathbb R\times\mathbb R^{d-1}$ satisfying Assumption 2.7 in its finite-horizon reading and Assumption 2.8.
--
--   **(A) Infinite horizon (Problem 2).** There is $v\in\mathcal A_d$ with
--
--   $$
--   v(x)=\sup_{\tau\in\mathcal T}\mathsf E_x\Big[e^{-r\tau}\max\{\varphi(X_\tau),(\Lambda v)(X_\tau)\}\Big]\qquad\text{for all }x\in\mathbb R^d,\tag{3}
--   $$
--
--   and every $w\in\mathcal A_d$ satisfying (3) equals $v$. Moreover, for every $x\in\mathbb R^d$:
--
--   1. the time $\tau_*=\inf\{s\ge0: v(X^x_s)=\max[\varphi(X^x_s),(\Lambda v)(X^x_s)]\}$ is an $\mathbb F$-stopping time and attains the supremum in (3) (payoff $0$ on $\{\tau_*=\infty\}$);
--   2. $t\mapsto e^{-rt}v(X^x_t)$, $t\in[0,\infty]$, is an $\mathbb F$-supermartingale under $\mathsf P$ (value $0$ at $t=\infty$) with right-continuous non-negative paths;
--   3. $t\mapsto e^{-r(t\wedge\tau_*)}v(X^x_{t\wedge\tau_*})$, $t\in[0,\infty)$, is an $\mathbb F$-martingale under $\mathsf P$ with right-continuous non-negative paths.
--
--   **(B) Finite horizon (Problem 2').** There is $v$ in the finite-horizon $\mathcal A_d$ satisfying the finite-horizon equation $v=\Gamma v$ on $[0,T]\times\mathbb R^{d-1}$, with $\Lambda$ from (12) and stopping times $\tau\le T-t$; any $w$ in that space satisfying it agrees with $v$ on $[0,T]\times\mathbb R^{d-1}$; and for every $z=(t,x)\in[0,T]\times\mathbb R^{d-1}$, the time $\tau_*$ (infimum over $s\in[0,T-t]$) is a stopping time with $\tau_*\le T-t$ a.s. attaining the supremum, while the two processes, indexed by $s\in[0,T-t]$, are a supermartingale and a martingale with right-continuous non-negative paths.
--
--   The theorem says that the recursive control/stopping problem with a random delay is well posed: its value is the unique fixed point of $\Gamma$ in the linear-growth class $\mathcal A_d$, and stopping at the first time the value meets the better of the immediate and the delayed payoff is optimal.
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
--   - encoding: (16): $v(X_s)=\max[\varphi(X_s),(\Lambda v)(X_s)]$ → $\mathrm{ofReal}(v(y))=\max\{\mathrm{ofReal}(\varphi(y)),(\Lambda v)(y)\}$ in $[0,\infty]$; reason: $\Lambda v$ is finite (Lemma 3.2), so the two sets coincide
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, Theorem 3.1, p.10 (finite horizon: §2.2, pp.9–10; remark on T < ∞, p.11)

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

/-- **Theorem 3.1**, Colaneri & De Angelis, arXiv:1905.02650v4, p.10: "Problem 2 (Problem 2')
admits a unique solution `v ∈ A_d`. Moreover, the stopping time
`τ_* = inf{s ≥ 0 : v(X_s) = max[ϕ(X_s), (Λv)(X_s)]}` (16) is optimal for (3), the process
`t ↦ e^{−rt}v(X_t)`, `t ∈ [0, ∞]` is a right-continuous (non-negative) `P_x`-supermartingale
and the process `t ↦ e^{−r(t∧τ_*)}v(X_{t∧τ_*})`, `t ∈ [0, ∞)` is a right-continuous
(non-negative) `P_x`-martingale, for any `x ∈ ℝ^d`."

Standing assumptions (both horizons): a probability space `(Ω, F, P)` with a filtration `𝔽`
satisfying the usual conditions of p.5, a delay law `μ` (a probability measure on `[0, ∞)`,
`F(t) = μ[0, t]`), `r > 0`, `p ∈ (0, 1)`. Infinite horizon: a flow `X` on `ℝ^d` with the process
axioms of p.5 and Assumption 2.7. Finite horizon (§2.2): `T ≥ 0`, a space-time flow `Z` on
`ℝ × ℝ^{d−1}` with the process axioms, Assumption 2.7 in the reading of pp.9–10, and
Assumption 2.8.

(A) Infinite horizon (Problem 2, (3)–(4), p.7): there is `v ∈ A_d` with `v(x) = (Γv)(x)` for all
`x`; every `w ∈ A_d` with `w = Γw` equals `v`; and for every `x`, with `G = max{ϕ, Λv}` and
`τ_*` the entry time of `{v = G}`: `τ_*` is an `𝔽`-stopping time attaining the supremum in (3)
(payoff `0` on `{τ_* = ∞}`), `t ↦ e^{−rt}v(X^x_t)` is an `𝔽`-supermartingale on `[0, ∞]` (value
`0` at `∞`) and `t ↦ e^{−r(t∧τ_*)}v(X^x_{t∧τ_*})` an `𝔽`-martingale on `[0, ∞)`, both with
right-continuous non-negative paths.

(B) Finite horizon (Problem 2', (12), p.9): the same on `[0, T] × ℝ^{d−1}`, with uniqueness
among `w ∈ A_d` on `[0, T] × ℝ^{d−1}`, `τ_*` the entry time before `T − t` (admissible,
`≤ T − t` a.s.), and both processes indexed by `s ∈ [0, T − t]` (frozen at `T − t`). -/
theorem theorem_3_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (h𝔽 : UsualConditions P 𝔽) (μ : Measure ℝ≥0)
    [IsProbabilityMeasure μ] (r p : ℝ) (hr : 0 < r) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ (d : ℕ) (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      MarkovFlow P 𝔽 X → ∀ ϕ ψ : EuclideanSpace ℝ (Fin d) → ℝ, Infinite.Assumption27 P 𝔽 X r ϕ ψ →
      ∃ v : EuclideanSpace ℝ (Fin d) → ℝ, Infinite.InA v ∧
        (∀ x, ENNReal.ofReal (v x) = Infinite.Gam P 𝔽 X μ r p ϕ ψ v x) ∧
        (∀ w, Infinite.InA w → (∀ x, ENNReal.ofReal (w x) = Infinite.Gam P 𝔽 X μ r p ϕ ψ w x) →
          w = v) ∧
        ∀ x,
          let G := fun y => max (ENNReal.ofReal (ϕ y)) (Infinite.Lam P X μ r p ψ v y)
          let τs := entryTime X x {y | ENNReal.ofReal (v y) = G y} ⊤
          let Y : ℝ≥0 → Ω → ℝ := fun t ω => Real.exp (-r * (t : ℝ)) * v (X x t ω)
          let Ys : ℝ≥0 → Ω → ℝ := fun t ω =>
            Real.exp (-r * (min (t : ℝ≥0∞) (τs ω)).toReal) *
              v (X x (min (t : ℝ≥0∞) (τs ω)).toNNReal ω)
          IsStoppingTime 𝔽 τs ∧
          ∫⁻ ω, discPayoff r G X x τs ω ∂P = ENNReal.ofReal (v x) ∧
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
      ∃ v : ℝ × EuclideanSpace ℝ (Fin m) → ℝ, Finite.InA T v ∧
        (∀ z ∈ Finite.Dom m T, ENNReal.ofReal (v z) = Finite.Gam P 𝔽 Z μ T r p ϕ ψ v z) ∧
        (∀ w, Finite.InA T w →
          (∀ z ∈ Finite.Dom m T, ENNReal.ofReal (w z) = Finite.Gam P 𝔽 Z μ T r p ϕ ψ w z) →
          ∀ z ∈ Finite.Dom m T, w z = v z) ∧
        ∀ z ∈ Finite.Dom m T,
          let G := fun y => max (ENNReal.ofReal (ϕ y)) (Finite.Lam P Z μ T r p ψ v y)
          let c : ℝ≥0∞ := ENNReal.ofReal (T - z.1)
          let τs := entryTime Z z {y | ENNReal.ofReal (v y) = G y} c
          let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
            Real.exp (-r * (min (s : ℝ≥0∞) c).toReal) * v (Z z (min (s : ℝ≥0∞) c).toNNReal ω)
          let Ys : ℝ≥0 → Ω → ℝ := fun s ω =>
            Real.exp (-r * (min (min (s : ℝ≥0∞) (τs ω)) c).toReal) *
              v (Z z (min (min (s : ℝ≥0∞) (τs ω)) c).toNNReal ω)
          IsStoppingTime 𝔽 τs ∧ (∀ᵐ ω ∂P, τs ω ≤ c) ∧
          ∫⁻ ω, discPayoff r G Z z τs ω ∂P = ENNReal.ofReal (v z) ∧
          Supermartingale Y 𝔽 P ∧
          (∀ ω (s : ℝ≥0), ContinuousWithinAt (fun u => Y u ω) (Set.Ici s) s) ∧
          (∀ s ω, 0 ≤ Y s ω) ∧
          Martingale Ys 𝔽 P ∧
          (∀ ω (s : ℝ≥0), ContinuousWithinAt (fun u => Ys u ω) (Set.Ici s) s) ∧
          (∀ s ω, 0 ≤ Ys s ω)) := by sorry

end RecursiveStopping
