-- Prove2me | Theorems.Thm_RecursiveStopping_Infinite_lam_lipschitz
-- name    : RecursiveStopping.Infinite.lam_lipschitz
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:43:35.132505+00:00
-- url     : https://prove2.me/theorems/58a3d3a0-f49f-4ed6-a5e3-8e6de4d35690
-- title:
--   From (33) — $\|\Lambda f-\Lambda g\|_{\mathcal A_d}\le(1-p)\|f-g\|_{\mathcal A_d}$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb F,\mathsf P)$ satisfy the usual conditions, let $X$ be a right-continuous, strong Markov, quasi left-continuous flow on $\mathbb R^d$, let $r>0$, and assume Assumption 2.7 for $X$, $r$ and payoffs $\varphi,\psi$. Let $p\in(0,1)$ and let $\mu$ be the law of the delay.
--
--   For all $f,g\in\mathcal A_d$,
--
--   $$
--   \|\Lambda f-\Lambda g\|_{\mathcal A_d}\le(1-p)\,\|f-g\|_{\mathcal A_d}.
--   $$
--
--   The factor $1-p$ is the probability that the delayed option fails and the problem restarts; it is the contraction constant of $\Gamma$.
--
--   Differences from the source:
--   - encoding: $\mathsf P_x$, $\mathsf E_x$ → the flow $X^x$ (or $Z^z$) under the single measure $\mathsf P$; reason: the paper defines $\mathsf E_x[f(X_\cdot)]=\mathsf E[f(X^x_\cdot)]$ (p.5)
--   - encoding: complete filtration → every set of $\mathsf P$-outer measure $0$ lies in $\mathcal F_0$; reason: the usual meaning of completeness
--   - encoding: expectations and the integral against $F(\mathrm dt)$ in (3), (4), (12), (15) → `lintegral` of $[0,\infty]$-valued integrands; equation (3) as $\mathrm{ofReal}(v(x))=(\Gamma v)(x)$; reason: all integrands are non-negative, so the values coincide and no default value can enter
--   - encoding: strong Markov property for any integrable functional → for bounded measurable path functionals, on $\{\tau<\infty\}$; reason: equivalent by truncation and monotone convergence; $X_{\tau+\cdot}$ is only defined on $\{\tau<\infty\}$
--   - reading: the flow $x\mapsto X^x_t$ is P-a.s. continuous for all $t\ge0$ → for each $t$, P-a.s. continuous; reason: word order of p.8; the paper uses it at fixed $t$ (p.9, Lemma 3.3)
--   - encoding: a non-negative random variable $\vartheta$ independent of $X$ with distribution function $F$ → a probability measure $\mu$ on $[0,\infty)$ with $F(t)=\mu[0,t]$; reason: only the law of $\vartheta$ enters (4) and (12)
--   - encoding: $\mathbb R^d$ with no bound on $d$ → `EuclideanSpace ℝ (Fin d)` for every $d\in\mathbb N$ (and $m=d-1\in\mathbb N$ in the finite horizon); reason: the Euclidean norm is $|\cdot|_d$; the source states no bound on $d$
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, display (33) and the sentence after it, p.15

import Mathlib
import Definitions.Def_RecursiveStopping_UsualConditions
import Definitions.Def_RecursiveStopping_MarkovFlow
import Definitions.Def_RecursiveStopping_Infinite_Assumption27
import Definitions.Def_RecursiveStopping_Infinite_Lam

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping.Infinite

/-- Colaneri & De Angelis, arXiv:1905.02650v4, p.15: "From (33) we deduce
`∥(Λf) − (Λg)∥_{A_d} ≤ (1 − p)∥f − g∥_{A_d}`".

Under the standing assumptions of §2 (infinite horizon), for all `f, g ∈ A_d`,
`∥Λf − Λg∥_{A_d} ≤ (1 − p)∥f − g∥_{A_d}`. -/
theorem lam_lipschitz {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ≥0 mΩ) (h𝔽 : UsualConditions P 𝔽)
    (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hX : MarkovFlow P 𝔽 X) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (r p : ℝ) (hr : 0 < r)
    (hp0 : 0 < p) (hp1 : p < 1) (ϕ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : Assumption27 P 𝔽 X r ϕ ψ)
    (f g : EuclideanSpace ℝ (Fin d) → ℝ) (hf : InA f) (hg : InA g) :
    wnorm (fun x => (Lam P X μ r p ψ f x).toReal - (Lam P X μ r p ψ g x).toReal)
      ≤ ENNReal.ofReal (1 - p) * wnorm (fun x => f x - g x) := by sorry

end RecursiveStopping.Infinite
