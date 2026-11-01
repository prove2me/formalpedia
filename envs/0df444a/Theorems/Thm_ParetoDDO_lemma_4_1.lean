-- Prove2me | Theorems.Thm_ParetoDDO_lemma_4_1
-- name    : ParetoDDO.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:21.825957+00:00
-- url     : https://prove2.me/theorems/b1360a0b-de18-423e-bb5d-d212e6b71254
-- title:
--   Lemma 4.1 — $\nabla_\lambda\Lambda(0,\theta)=\lim_T\mathbb E_\theta[\widehat S_T]$
-- statement:
--   Assume Assumption 2.1, let $\widehat S$ be a statistic and let Assumption 4.2 hold. Then for every $\theta\in\Theta$
--   $$
--   \nabla_\lambda\Lambda(0,\theta)=\lim_{T\to\infty}\mathbb E_\theta[\widehat S_T].
--   $$
--
--   The gradient at the origin is the asymptotic mean of the statistic.
--
--   **Formalization Note** The conclusion also records that each $\widehat S_T$ is $\mathbb P_\theta$-integrable. The gradient is that of the real-valued $\Lambda(\cdot,\theta)$, which is finite near $0$.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: Assumption 4.2 defines $\Lambda$ as the limit (4.3) → a function `Λ` with `IsLogMGFRegular P Θ Ŝ Λ`, which states that (4.3) converges to it; reason: the limit is unique, so quantifying over such $\Lambda$ is the same as using the limit
--   - reading: $\lim_T\mathbb E_\theta[\widehat S_T]$ → integrability of each $\widehat S_T$ as a conjunct, then convergence of the expectations to $\nabla_\lambda\Lambda(0,\theta)$; reason: the printed formula presupposes the expectations exist; Lean's integral would otherwise default to $0$
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Lemma 4.1, p.24

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_ExpFamily

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Lemma 4.1** (Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.24). If Assumption 4.2 holds, then
`∇_λ Λ(0, θ) = lim_T E_θ[Ŝ_T]` for all `θ ∈ Θ`.

**Formalization Note** The conclusion also records that each `Ŝ_T` is `P_θ`-integrable, so `E_θ[Ŝ_T]`
is a genuine expectation. The gradient is that of the real-valued `Λ(·, θ)` near `0`. -/
theorem lemma_4_1
    {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (Λ : Vec d → Vec d → EReal) (h42 : IsLogMGFRegular P Θ Ŝ Λ) :
    ∀ θ ∈ Θ, (∀ T, 1 ≤ T → Integrable (Ŝ T) (P θ)) ∧
      Tendsto (fun T => ∫ ω, Ŝ T ω ∂(P θ)) atTop
        (𝓝 (gradient (fun v => (Λ v θ).toReal) 0)) := by sorry

end ParetoDDO
