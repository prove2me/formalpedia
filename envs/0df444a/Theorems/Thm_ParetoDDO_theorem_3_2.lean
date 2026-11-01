-- Prove2me | Theorems.Thm_ParetoDDO_theorem_3_2
-- name    : ParetoDDO.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:24.533679+00:00
-- url     : https://prove2.me/theorems/96356c18-f37a-4cb1-80ac-9aa8a848eef4
-- title:
--   Theorem 3.2 — $(\tilde c^\star,\tilde x^\star)$ is Pareto dominant in the restricted problem (2.6b)
-- statement:
--   Assume Assumptions 2.1 and 2.2, and Assumption 3.1: the statistic $\widehat S$ satisfies an LDP with a regular rate function $I$. Let $r>0$, let $\tilde c^\star$ be the distributionally robust predictor (3.3) and $\tilde x^\star$ any distributionally robust prescriptor (3.4). Then $(\tilde c^\star,\tilde x^\star)$ is a Pareto dominant solution of (2.6b):
--
--   1. **feasibility:** $(\tilde c^\star,\tilde x^\star)\in\tilde{\mathcal X}$ and for every $\theta\in\Theta$
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P_\theta\big[c(\tilde x^\star(\widehat S_T),\theta)>\tilde c^\star(\tilde x^\star(\widehat S_T),\widehat S_T)\big]\le-r;
--   $$
--   2. **dominance:** for every feasible $(\tilde c,\tilde x)$ of (2.6b) and every $\theta\in\Theta$,
--   $$
--   \tilde c^\star(\tilde x^\star(S_\infty(\theta)),S_\infty(\theta))\le\tilde c(\tilde x(S_\infty(\theta)),S_\infty(\theta)).
--   $$
--
--   The feasibility half is used in the proof of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $X\subseteq\mathbb R^n$ compact, with $\min_{x\in X}$ used throughout → $X$ compact and nonempty; reason: the paper's minima over $X$ presuppose $X\neq\emptyset$; for empty $X$ the source's objects are undefined
--   - encoding: Assumption 2.2 on $X\times\Theta$, and $c$ also denotes its unique extension to $X\times\operatorname{cl}\Theta$ (p.12) → `c` is bounded and uniformly continuous on $X\times\operatorname{cl}\Theta$; reason: equivalent: the extension is unique and stays bounded and uniformly continuous, and the paper uses the extension
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: $I:\mathbb S\times\operatorname{cl}\Theta\to[0,\infty]$ → `I : ℝ^d → ℝ^d → ℝ≥0∞`, only its values on $\mathbb S\times\operatorname{cl}\Theta$ are used; reason: Lean functions are total; the definitions read $I$ only on $\mathbb S\times\operatorname{cl}\Theta$
--   - encoding: $\max_{\theta\in\operatorname{cl}\Theta}\{c(x,\theta):I(s,\theta)\le r\}$ in (3.3) → `sSup` of the image of the feasible set; reason: the maximum is attained (p.21), so it equals the supremum
--   - encoding: $\frac1T\log\mathbb P_\theta[\cdot]$ → `ENNReal.log` into $[-\infty,\infty]$, so $\log 0=-\infty$; reason: the source's convention; a real logarithm would send $\log 0$ to $0$
--   - encoding: $\mathbb P_\theta[E]$ for events $E$ → outer measure `P θ E` of an arbitrary set; reason: agrees with the measure on measurable events; events built from quasi-continuous maps need not be measurable
--   - reading: $\operatorname{int}\mathcal D$, $\operatorname{cl}\mathcal D$ in (3.1) → interior and closure relative to $\mathbb S$ (`relInterior S D`, `closure D ∩ S`); reason: §3.1 works in the subspace topology of $\mathbb S$ (p.19); for the closed set $\mathbb S$ the relative closure is the closure
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Theorem 3.2, p.22; Assumption 3.1, p.21

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_RateFunction
import Definitions.Def_ParetoDDO_DRPredictor

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Theorem 3.2** (optimality of `(c̃⋆, x̃⋆)`; Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.22). If Assumptions 2.1,
2.2 and 3.1 hold (`Ŝ` satisfies an LDP with a regular rate function `I`) and `r > 0`, then for every
distributionally robust prescriptor `x̃⋆` (Definition 3.5) the pair `(c̃⋆, x̃⋆)` is a Pareto dominant
solution of the restricted meta-optimization problem (2.6b). -/
theorem theorem_3_2
    {Ω : Type*} [MeasurableSpace Ω] {m n d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (X : Set (Vec n)) (hX : IsCompact X) (hXne : X.Nonempty)
    (c : Vec n → Vec d → ℝ) (hc : IsModelPredictor X Θ c)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (I : Vec d → Vec d → ℝ≥0∞) (hLDP : IsLDP P Θ Ŝ S I)
    (hIreg : IsRegularRateFunction S Θ Sinf I)
    (r : ℝ) (hr : 0 < r)
    (xt : Vec d → Vec n) (hxt : IsDRPrescriptor X S Sinf Θ c I r xt) :
    IsParetoDominant26b P Θ Ŝ S Sinf X c r (drPredictor c Θ I r) xt := by sorry

end ParetoDDO
