-- Prove2me | Theorems.Thm_ParetoDDO_theorem_4_3
-- name    : ParetoDDO.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:23.360985+00:00
-- url     : https://prove2.me/theorems/a2b4ff80-2256-4fdf-9ca2-794cad0f462f
-- title:
--   Theorem 4.3 — $(\widehat c^\star,\widehat x^\star)$ is Pareto dominant in (2.4b) (corrected: DR prescriptor Borel)
-- statement:
--   Assume Assumptions 2.1 and 2.2, let $\widehat S$ be a statistic with closed state space $\mathbb S$ and asymptotic map $S_\infty$, and let Assumptions 4.1 and 4.2 hold. Let $I:\mathbb S\times\operatorname{cl}\Theta\to[0,\infty]$ be a regular rate function (Definition 3.3) that agrees with the Gärtner–Ellis rate (4.4) on $\mathbb S\times\Theta$, and let $r>0$. Let $\tilde c^\star$ be the distributionally robust predictor (3.3) and $\tilde x^\star$ a distributionally robust prescriptor (3.4) that is Borel measurable on $\mathbb S$. Define
--   $$
--   \widehat c^\star_T(x)=\tilde c^\star(x,\widehat S_T),\qquad\widehat x^\star_T=\tilde x^\star(\widehat S_T).
--   $$
--   Then $(\widehat c^\star,\widehat x^\star)$ is a Pareto dominant solution of the meta-optimization problem (2.4b):
--
--   1. **feasibility:** $(\widehat c^\star,\widehat x^\star)\in\widehat{\mathcal X}$, and for every $\theta\in\Theta$
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P_\theta\big[c(\widehat x^\star_T,\theta)>\widehat c^\star_T(\widehat x^\star_T)\big]\le-r;
--   $$
--   2. **dominance:** for every pair $(\widehat c,\widehat x)\in\widehat{\mathcal X}$ that is feasible in (2.4b) and every $\theta\in\Theta$, both in-sample risks are integrable, both limits $\lim_T\mathbb E_\theta[\widehat c^\star_T(\widehat x^\star_T)]$ and $\lim_T\mathbb E_\theta[\widehat c_T(\widehat x_T)]$ exist, and
--   $$
--   \lim_{T\to\infty}\mathbb E_\theta[\widehat c^\star_T(\widehat x^\star_T)]\le\lim_{T\to\infty}\mathbb E_\theta[\widehat c_T(\widehat x_T)].
--   $$
--
--   Among all ways of mapping the data to a cost estimate and a decision, the distributionally robust pair built from the statistic and its rate function is simultaneously best for every model.
--
--   Differences from the source:
--   - correction: $\tilde x^\star$ any distributionally robust prescriptor (Definition 3.5) → $\tilde x^\star$ a distributionally robust prescriptor that is Borel measurable on $\mathbb S$; reason: counterexample satisfying every assumption of the source: Gaussian mean, $d=1$, $\Theta=(-1,1)$, $\xi_t$ i.i.d. $N(\theta,1)$, $\widehat S_T$ the sample mean ($\mathbb S=\mathbb R$, $S_\infty(\theta)=\theta$), $\bar\theta=0$, $g(\theta)=\theta$, $A_T(\lambda)=\lambda^2/(2T)$, $\Lambda(\lambda,\theta)=\lambda\theta+\lambda^2/2$, $I(s,\theta)=(s-\theta)^2/2$ (regular on $\mathbb R\times[-1,1]$), $X=[0,1]$, $c\equiv0$, $r=1$: then $\tilde c^\star\equiv0$ and $\tilde x^\star=\mathbf 1_N$ with $N\subseteq[2,3]$ not Lebesgue measurable is a DR prescriptor (constant on $S_\infty$), but $\{\widehat x^\star_1=1\}=\xi_1^{-1}(N)\notin\mathcal F_1$, so $(\widehat c^\star,\widehat x^\star)\notin\widehat{\mathcal X}$
--   - reading: "the rate function (4.4) is regular", with (4.4) defined on $\mathbb R^d\times\Theta$ and Definition 3.3 on $\mathbb S\times\operatorname{cl}\Theta$ → every regular rate function $I$ on $\mathbb S\times\operatorname{cl}\Theta$ that agrees with (4.4) on $\mathbb S\times\Theta$; $\tilde c^\star$, $\tilde x^\star$ are built from that $I$; reason: the paper extends (4.4) to $\operatorname{cl}\Theta$ to make it a (regular) rate function (p.24); the theorem is stated for every such extension
--   - encoding: Assumption 4.1: there exist $\bar\theta$ and $g$ → hypothesis `∃ θbar g, IsExpFamily ξ P Θ Ŝ θbar g`; reason: the same assumption
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $X\subseteq\mathbb R^n$ compact, with $\min_{x\in X}$ used throughout → $X$ compact and nonempty; reason: the paper's minima over $X$ presuppose $X\neq\emptyset$; for empty $X$ the source's objects are undefined
--   - encoding: Assumption 2.2 on $X\times\Theta$, and $c$ also denotes its unique extension to $X\times\operatorname{cl}\Theta$ (p.12) → `c` is bounded and uniformly continuous on $X\times\operatorname{cl}\Theta$; reason: equivalent: the extension is unique and stays bounded and uniformly continuous, and the paper uses the extension
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: Assumption 4.2 defines $\Lambda$ as the limit (4.3) → a function `Λ` with `IsLogMGFRegular P Θ Ŝ Λ`, which states that (4.3) converges to it; reason: the limit is unique, so quantifying over such $\Lambda$ is the same as using the limit
--   - encoding: $I:\mathbb S\times\operatorname{cl}\Theta\to[0,\infty]$ → `I : ℝ^d → ℝ^d → ℝ≥0∞`, only its values on $\mathbb S\times\operatorname{cl}\Theta$ are used; reason: Lean functions are total; the definitions read $I$ only on $\mathbb S\times\operatorname{cl}\Theta$
--   - encoding: $\max_{\theta\in\operatorname{cl}\Theta}\{c(x,\theta):I(s,\theta)\le r\}$ in (3.3) → `sSup` of the image of the feasible set; reason: the maximum is attained (p.21), so it equals the supremum
--   - encoding: $\frac1T\log\mathbb P_\theta[\cdot]$ → `ENNReal.log` into $[-\infty,\infty]$, so $\log 0=-\infty$; reason: the source's convention; a real logarithm would send $\log 0$ to $0$
--   - encoding: $\mathbb P_\theta[E]$ for events $E$ → outer measure `P θ E` of an arbitrary set; reason: agrees with the measure on measurable events; events built from quasi-continuous maps need not be measurable
--   - encoding: the objective $\lim_{T}\mathbb E_\theta[\widehat c_T(\widehat x_T)]$, "well-defined" (p.16) → integrability of both in-sample risks for $T\ge1$, convergence of both sequences of expectations, and comparison of the limits; reason: states the existence the paper asserts instead of using a junk-valued `limUnder`
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Theorem 4.3, p.26 (ĉ⋆ defined p.25, x̂⋆ p.26)

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_DataDriven
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_RateFunction
import Definitions.Def_ParetoDDO_DRPredictor
import Definitions.Def_ParetoDDO_ExpFamily

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Theorem 4.3** (optimality of `(ĉ⋆, x̂⋆)`; Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.26), corrected.
If Assumptions 2.1, 2.2, 4.1 and 4.2 hold, the rate function (4.4) is regular and `r > 0`, then
`(ĉ⋆, x̂⋆)` is a Pareto dominant solution of the meta-optimization problem (2.4b). Here
`ĉ⋆_T(x) = c̃⋆(x, Ŝ_T)` (p.25) and `x̂⋆_T = x̃⋆(Ŝ_T)` (p.26) for the distributionally robust predictor
`c̃⋆` (3.3) and a distributionally robust prescriptor `x̃⋆` (3.4).

**Formalization Note** "The rate function (4.4) is regular" is read as: `I : S × cl Θ → [0, ∞]` is a
regular rate function that agrees with (4.4) on `S × Θ` (the paper extends (4.4) to `cl Θ`, p.24);
the theorem is stated for every such extension. Correction: `x̃⋆` is Borel measurable on `S`;
without it `x̂⋆` need not be adapted and the printed statement is false. -/
theorem theorem_4_3
    {Ω : Type*} [MeasurableSpace Ω] {m n d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (X : Set (Vec n)) (hX : IsCompact X) (hXne : X.Nonempty)
    (c : Vec n → Vec d → ℝ) (hc : IsModelPredictor X Θ c)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (h41 : ∃ (θbar : Vec d) (g : Vec d → Vec d), IsExpFamily ξ P Θ Ŝ θbar g)
    (Λ : Vec d → Vec d → EReal) (h42 : IsLogMGFRegular P Θ Ŝ Λ)
    (I : Vec d → Vec d → ℝ≥0∞) (hIreg : IsRegularRateFunction S Θ Sinf I)
    (hIext : ∀ s ∈ S, ∀ θ ∈ Θ, (I s θ : EReal) = gartnerEllisRate Λ s θ)
    (r : ℝ) (hr : 0 < r)
    (xt : Vec d → Vec n) (hxt : IsDRPrescriptor X S Sinf Θ c I r xt)
    (hxt_meas : Measurable (S.domRestrict xt)) :
    IsParetoDominant24b ξ P Θ X c r (inducedPredictor (drPredictor c Θ I r) Ŝ)
      (inducedPrescriptor xt Ŝ) := by sorry

end ParetoDDO
