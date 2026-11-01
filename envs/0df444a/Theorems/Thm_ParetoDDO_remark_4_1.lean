-- Prove2me | Theorems.Thm_ParetoDDO_remark_4_1
-- name    : ParetoDDO.remark_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:26.341191+00:00
-- url     : https://prove2.me/theorems/34321b1a-f2c2-4657-af0c-5e19606f1504
-- title:
--   Remark 4.1 — the gradient of $\Lambda(\cdot,\theta)$ at a tilt $\eta=g(\theta')-g(\theta)$
-- statement:
--   Assume Assumption 2.1, let $\widehat S$ be a statistic and let Assumptions 4.1 (with $\bar\theta$, $g$) and 4.2 hold. For $\theta,\theta'\in\Theta$ and $\eta=g(\theta')-g(\theta)$:
--
--   1. $\eta$ lies in the interior of $\operatorname{dom}\Lambda(\cdot,\theta)$, so $\nabla_\lambda\Lambda(\eta,\theta)$ exists;
--   2. the random vectors $\widehat S_T\exp(\langle\eta,T\widehat S_T\rangle-\Lambda_T(T\eta,\theta))$ are $\mathbb P_\theta$-integrable;
--   3. $$
--   \nabla_\lambda\big[\Lambda(\lambda,\theta)\big]_{\lambda=\eta}=\lim_{T\to\infty}\mathbb E_\theta\big[\widehat S_T\cdot\exp(\langle\eta,T\widehat S_T\rangle-\Lambda_T(T\eta,\theta))\big].
--   $$
--
--   This generalizes Lemma 4.1 from the origin to exponential tilts.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: Assumption 4.2 defines $\Lambda$ as the limit (4.3) → a function `Λ` with `IsLogMGFRegular P Θ Ŝ Λ`, which states that (4.3) converges to it; reason: the limit is unique, so quantifying over such $\Lambda$ is the same as using the limit
--   - reading: the identity $\nabla_\lambda[\Lambda(\lambda,\theta)]_{\lambda=\eta}=\lim_T\mathbb E_\theta[\dots]$ → also $\eta\in\operatorname{int}\operatorname{dom}\Lambda(\cdot,\theta)$ and integrability of the integrands, as conjuncts; reason: the printed formula presupposes that the gradient at $\eta$ and the expectations exist
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Remark 4.1, p.24

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_ExpFamily

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Remark 4.1** (Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.24). If Assumptions 4.1 and 4.2 hold and
`η = g(θ') − g(θ)` for some `θ, θ' ∈ Θ`, then
`∇_λ[Λ(λ, θ)]_{λ=η} = lim_T E_θ[Ŝ_T · exp(⟨η, T Ŝ_T⟩ − Λ_T(Tη, θ))]`.

**Formalization Note** The conclusion also states that `η` lies in the interior of `dom Λ(·, θ)` (so
the gradient exists by Assumption 4.2) and that the integrands are `P_θ`-integrable. -/
theorem remark_4_1
    {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (θbar : Vec d) (g : Vec d → Vec d) (h41 : IsExpFamily ξ P Θ Ŝ θbar g)
    (Λ : Vec d → Vec d → EReal) (h42 : IsLogMGFRegular P Θ Ŝ Λ)
    (θ θ' : Vec d) (hθ : θ ∈ Θ) (hθ' : θ' ∈ Θ) :
    g θ' - g θ ∈ interior {u : Vec d | Λ u θ ≠ ⊤} ∧
      (∀ T : ℕ, 1 ≤ T → Integrable (fun ω => Real.exp (⟪g θ' - g θ, (T : ℝ) • Ŝ T ω⟫ -
        (logMGF (P θ) (Ŝ T) ((T : ℝ) • (g θ' - g θ))).toReal) • Ŝ T ω) (P θ)) ∧
      Tendsto (fun T : ℕ => ∫ ω, Real.exp (⟪g θ' - g θ, (T : ℝ) • Ŝ T ω⟫ -
          (logMGF (P θ) (Ŝ T) ((T : ℝ) • (g θ' - g θ))).toReal) • Ŝ T ω ∂(P θ)) atTop
        (𝓝 (gradient (fun v => (Λ v θ).toReal) (g θ' - g θ))) := by sorry

end ParetoDDO
