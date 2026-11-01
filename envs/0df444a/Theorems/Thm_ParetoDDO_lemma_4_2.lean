-- Prove2me | Theorems.Thm_ParetoDDO_lemma_4_2
-- name    : ParetoDDO.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:21.773334+00:00
-- url     : https://prove2.me/theorems/677bcbf6-07c0-4562-98b4-30ec272d6111
-- title:
--   Lemma 4.2 — $\widehat S_T\to\nabla_\lambda\Lambda(0,\theta)$, so $S_\infty(\theta)=\nabla_\lambda\Lambda(0,\theta)$
-- statement:
--   Assume Assumption 2.1, let $\widehat S$ be a statistic with asymptotic map $S_\infty$, and let Assumption 4.2 hold. Then for every $\theta\in\Theta$
--
--   1. $\widehat S_T\to\nabla_\lambda\Lambda(0,\theta)$ in $\mathbb P_\theta$-probability, and
--   2. $S_\infty(\theta)=\nabla_\lambda\Lambda(0,\theta)$.
--
--   The asymptotic realization of the statistic is determined by $\Lambda$.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: Assumption 4.2 defines $\Lambda$ as the limit (4.3) → a function `Λ` with `IsLogMGFRegular P Θ Ŝ Λ`, which states that (4.3) converges to it; reason: the limit is unique, so quantifying over such $\Lambda$ is the same as using the limit
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Lemma 4.2, p.25

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_ExpFamily

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Lemma 4.2** (asymptotic consistency of `Ŝ`; Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.25). If
Assumption 4.2 holds, then `Ŝ_T → ∇_λ Λ(0, θ)` in `P_θ`-probability for every `θ ∈ Θ`, and hence
`S∞(θ) = ∇_λ Λ(0, θ)`. -/
theorem lemma_4_2
    {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (Λ : Vec d → Vec d → EReal) (h42 : IsLogMGFRegular P Θ Ŝ Λ) :
    ∀ θ ∈ Θ, TendstoInMeasure (P θ) Ŝ atTop (fun _ => gradient (fun v => (Λ v θ).toReal) 0) ∧
      Sinf θ = gradient (fun v => (Λ v θ).toReal) 0 := by sorry

end ParetoDDO
