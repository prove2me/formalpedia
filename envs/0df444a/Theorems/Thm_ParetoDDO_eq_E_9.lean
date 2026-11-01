-- Prove2me | Theorems.Thm_ParetoDDO_eq_E_9
-- name    : ParetoDDO.eq_E_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:10.71393+00:00
-- url     : https://prove2.me/theorems/fe3d1993-1489-43c4-ab32-fcbc04c8c74a
-- title:
--   (E.9) — change of measure bounds the decay rate under $\theta^\star_0$ from below
-- statement:
--   Assume Assumption 2.1, let $\widehat S$ be a statistic and let Assumptions 4.1 (with $\bar\theta$, $g$) and 4.2 hold. Let $\theta_0,\theta^\star_0\in\Theta$, $\eta=g(\theta_0)-g(\theta^\star_0)$, $s_0\in\mathbb R^d$, $\delta>0$, and let $E_T\in\mathcal F_T$ be events with $E_T\subseteq\{\|\widehat S_T-s_0\|\le\delta\}$. Then
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P_{\theta^\star_0}(E_T)\ \ge\ \Lambda(\eta,\theta^\star_0)-\langle\eta,s_0\rangle-\|\eta\|\delta+\limsup_{T\to\infty}\frac1T\log\mathbb P_{\theta_0}(E_T).
--   $$
--
--   In the proof of Theorem 4.3 this transfers the non-vanishing probability of a competitor's good event under $\theta_0$ into a slow decay of its disappointment under $\theta^\star_0$.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: Assumption 4.2 defines $\Lambda$ as the limit (4.3) → a function `Λ` with `IsLogMGFRegular P Θ Ŝ Λ`, which states that (4.3) converges to it; reason: the limit is unique, so quantifying over such $\Lambda$ is the same as using the limit
--   - encoding: $\frac1T\log\mathbb P_\theta[\cdot]$ → `ENNReal.log` into $[-\infty,\infty]$, so $\log 0=-\infty$; reason: the source's convention; a real logarithm would send $\log 0$ to $0$
--   - generalization: the event $\{\widehat c_T(\widehat x_T)<v_\infty(\theta_0)+\varepsilon\wedge\widehat S_T\in B_\delta(s_0)\wedge\|\widehat x_T-x_0\|<\rho\}$ with the open ball $B_\delta(s_0)$ → every sequence of events $E_T\in\mathcal F_T$ inside the closed ball $\{\|\widehat S_T-s_0\|\le\delta\}$; reason: the paper's event is $\mathcal F_T$-measurable and lies in the closed ball, so it is a special case
--   - encoding: sums of decay rates and constants → arithmetic in $[-\infty,\infty]$ (`EReal`); reason: a decay rate may be $-\infty$; $\Lambda(\eta,\theta^\star_0)$ is finite under the hypotheses
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, second inequality of (E.9), p.47; the change of measure (E.4)–(E.5), p.45

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_ExpFamily

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **The change-of-measure bound in (E.9)** (Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.47; the argument of
(E.4)–(E.5), p.45). Under Assumptions 4.1 and 4.2, let `θ₀, θ⋆₀ ∈ Θ`, `η = g(θ₀) − g(θ⋆₀)`,
`s₀ ∈ ℝ^d` and `δ > 0`. For events `E_T ∈ F_T` contained in `{‖Ŝ_T − s₀‖ ≤ δ}`,
`limsup_T (1/T) log P_θ⋆₀(E_T) ≥ Λ(η, θ⋆₀) − ⟨η, s₀⟩ − ‖η‖δ + limsup_T (1/T) log P_θ₀(E_T)`.

**Formalization Note** The inequality is in `[−∞, ∞]` (`log 0 = −∞`). The paper applies it to one
event inside the open ball `B_δ(s₀)`; it is stated here for every such sequence of events in the
closed ball. -/
theorem eq_E_9
    {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (θbar : Vec d) (g : Vec d → Vec d) (h41 : IsExpFamily ξ P Θ Ŝ θbar g)
    (Λ : Vec d → Vec d → EReal) (h42 : IsLogMGFRegular P Θ Ŝ Λ)
    (θ₀ θ' : Vec d) (hθ₀ : θ₀ ∈ Θ) (hθ' : θ' ∈ Θ) (s₀ : Vec d) (δ : ℝ) (hδ : 0 < δ)
    (E : ℕ → Set Ω) (hE : ∀ T, 1 ≤ T → MeasurableSet[histSigma ξ T] (E T))
    (hEsub : ∀ T, 1 ≤ T → E T ⊆ {ω | ‖Ŝ T ω - s₀‖ ≤ δ}) :
    Λ (g θ₀ - g θ') θ' - ((⟪g θ₀ - g θ', s₀⟫ + ‖g θ₀ - g θ'‖ * δ : ℝ) : EReal) +
        decayRate (P θ₀) E ≤ decayRate (P θ') E := by sorry

end ParetoDDO
