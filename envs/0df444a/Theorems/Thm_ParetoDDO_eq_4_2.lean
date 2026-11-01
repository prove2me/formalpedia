-- Prove2me | Theorems.Thm_ParetoDDO_eq_4_2
-- name    : ParetoDDO.eq_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:18.045903+00:00
-- url     : https://prove2.me/theorems/0c066b96-bf26-4856-8fcd-597c7a1ba620
-- title:
--   (4.2) — $\Lambda_T(\lambda,\theta)=A_T(\lambda+Tg(\theta))-A_T(Tg(\theta))$
-- statement:
--   Assume Assumption 2.1, let $\widehat S$ be a statistic, and let Assumption 4.1 hold with baseline model $\bar\theta$, parametrization $g$ and log-partition functions $A_T=\Lambda_T(\cdot,\bar\theta)$. Then for all $T\in\mathbb N$, $\theta\in\Theta$ and $\lambda\in\mathbb R^d$
--   $$
--   \Lambda_T(\lambda,\theta)=A_T(\lambda+Tg(\theta))-A_T(Tg(\theta)).
--   $$
--
--   Every model's log-moment generating function is a shift of the log-partition function.
--
--   **Formalization Note** Both sides are in $(-\infty,\infty]$; $A_T(Tg(\theta))$ is finite, so both sides are $+\infty$ together.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: $\Lambda_T$, $A_T$ with values in $(-\infty,+\infty]$ → `EReal`-valued `logMGF`, with $+\infty-a=+\infty$ for finite $a$; reason: the source's convention; the subtracted term is finite
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, (4.2), p.23

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_ExpFamily

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Equation (4.2)** (Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.23). Under Assumption 4.1 with baseline `θ̄` and
parametrization `g`, every log-moment generating function is recovered from the log-partition
function `A_T = Λ_T(·, θ̄)`: `Λ_T(λ, θ) = A_T(λ + T g(θ)) − A_T(T g(θ))` for all `T`, `θ ∈ Θ`,
`λ ∈ ℝ^d`.

**Formalization Note** Values are in `(−∞, ∞]`; `A_T(T g(θ))` is finite, so the right side is `+∞`
exactly when `A_T(λ + T g(θ))` is. -/
theorem eq_4_2
    {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (θbar : Vec d) (g : Vec d → Vec d) (h41 : IsExpFamily ξ P Θ Ŝ θbar g) :
    ∀ θ ∈ Θ, ∀ T : ℕ, 1 ≤ T → ∀ u : Vec d,
      logMGF (P θ) (Ŝ T) u = logMGF (P θbar) (Ŝ T) (u + (T : ℝ) • g θ) -
        logMGF (P θbar) (Ŝ T) ((T : ℝ) • g θ) := by sorry

end ParetoDDO
