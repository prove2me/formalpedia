-- Prove2me | Theorems.Thm_ParetoDDO_rate_at_tilt
-- name    : ParetoDDO.rate_at_tilt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:20.556029+00:00
-- url     : https://prove2.me/theorems/906c816c-754e-4035-957f-8849dc09574e
-- title:
--   Proof of Theorem 4.2 — $I(s_0,\theta^\star_0)=\langle\eta,s_0\rangle-\Lambda(\eta,\theta^\star_0)$
-- statement:
--   Assume Assumption 2.1, let $\widehat S$ be a statistic and let Assumptions 4.1 (with $\bar\theta$, $g$) and 4.2 hold. For $\theta_0,\theta^\star_0\in\Theta$, $s_0=S_\infty(\theta_0)$ and $\eta=g(\theta_0)-g(\theta^\star_0)$, the tilt $\eta$ attains the supremum in (4.4):
--   $$
--   I(s_0,\theta^\star_0)=\sup_{\lambda\in\mathbb R^d}\langle\lambda,s_0\rangle-\Lambda(\lambda,\theta^\star_0)=\langle\eta,s_0\rangle-\Lambda(\eta,\theta^\star_0).
--   $$
--
--   This closes the proof of Theorem 4.3: the competitor's disappointment under $\theta^\star_0$ decays at rate at most $I(s_0,\theta^\star_0)<r$.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: Assumption 4.2 defines $\Lambda$ as the limit (4.3) → a function `Λ` with `IsLogMGFRegular P Θ Ŝ Λ`, which states that (4.3) converges to it; reason: the limit is unique, so quantifying over such $\Lambda$ is the same as using the limit
--   - encoding: (4.4) and $\Lambda$ with values in $(-\infty,\infty]$ → `EReal` supremum and subtraction; reason: the equality forces $\Lambda(\eta,\theta^\star_0)$ finite, as in the source
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, proof of Theorem 4.2, pp.45–46; used in the proof of Theorem 4.3, p.47

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_ExpFamily

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **The rate at the exponential tilt** (Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, proof of Theorem 4.2,
pp.45–46, used in the proof of Theorem 4.3, p.47). Under Assumptions 4.1 and 4.2, for `θ₀, θ⋆₀ ∈ Θ`
with `s₀ = S∞(θ₀)` and `η = g(θ₀) − g(θ⋆₀)`, the tilt `η` attains the supremum in (4.4):
`I(s₀, θ⋆₀) = ⟨η, s₀⟩ − Λ(η, θ⋆₀)`. -/
theorem rate_at_tilt
    {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (θbar : Vec d) (g : Vec d → Vec d) (h41 : IsExpFamily ξ P Θ Ŝ θbar g)
    (Λ : Vec d → Vec d → EReal) (h42 : IsLogMGFRegular P Θ Ŝ Λ)
    (θ₀ θ' : Vec d) (hθ₀ : θ₀ ∈ Θ) (hθ' : θ' ∈ Θ) :
    gartnerEllisRate Λ (Sinf θ₀) θ' =
      ((⟪g θ₀ - g θ', Sinf θ₀⟫ : ℝ) : EReal) - Λ (g θ₀ - g θ') θ' := by sorry

end ParetoDDO
