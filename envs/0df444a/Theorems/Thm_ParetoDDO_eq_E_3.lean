-- Prove2me | Theorems.Thm_ParetoDDO_eq_E_3
-- name    : ParetoDDO.eq_E_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:35:24.638986+00:00
-- url     : https://prove2.me/theorems/1f7f007b-6769-4659-a9ad-fe57e11be584
-- title:
--   (E.3) — the density of $\mathbb P^T_{\theta}$ with respect to $\mathbb P^T_{\theta'}$
-- statement:
--   Assume Assumption 2.1, let $\widehat S$ be a statistic and let Assumption 4.1 hold with $\bar\theta$, $g$. For $\theta,\theta'\in\Theta$, $T\in\mathbb N$ and $\eta=g(\theta)-g(\theta')$, the value $\Lambda_T(T\eta,\theta')$ is finite and
--   $$
--   \frac{d\mathbb P^T_{\theta}}{d\mathbb P^T_{\theta'}}=\exp\big(\langle\eta,T\widehat S_T\rangle-\Lambda_T(T\eta,\theta')\big).
--   $$
--
--   This is the exponential tilting that moves a competitor's disappointment from one model to another.
--
--   **Formalization Note** The density identity is stated setwise over $A\in\mathcal F_T$; the finiteness of $\Lambda_T(T\eta,\theta')$ is a conjunct. In the paper $\theta=\theta_0$ and $\theta'=\theta^\star_0$.
--
--   Differences from the source:
--   - encoding: time $T\in\mathbb N=\{1,2,\dots\}$ → `T : ℕ` with every condition imposed for $1\le T$; the $T=0$ slice is unconstrained; reason: Lean's ℕ contains 0; limits ignore one term, so the objects are the same
--   - encoding: $\mathbb P_\star\in\mathcal P$ (Assumption 2.1) → $\Theta\neq\emptyset$; $\mathbb P_\star$ is not represented; reason: $\mathbb P_\star$ enters no statement of the mission; its existence only gives $\Theta\neq\emptyset$
--   - encoding: $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ (p.16) → $\widehat S_T(\omega)\in\mathbb S$ for every $\omega$ and $T\ge1$; reason: changing $\widehat S_T$ on an $\mathcal F_T$-set that is null for every $\theta$ changes no probability or expectation, and $\tilde c$, $\tilde x$ are only defined on $\mathbb S$
--   - encoding: the standing statistic $\widehat S$ of §2.3–§4 with state space $\mathbb S$ and $S_\infty$ → `IsStatistic ξ P Θ Ŝ S Sinf` as a hypothesis; reason: the result is stated in the paper's standing setting, where $\widehat S$ is a statistic (Definition 2.5)
--   - encoding: $\frac{d\mathbb P^T_{\theta_0}}{d\mathbb P^T_{\theta^\star_0}}=\exp(\dots)$ → $\mathbb P_\theta(A)=\int_A\exp(\dots)\,d\mathbb P_{\theta'}$ for every $A\in\mathcal F_T$, plus finiteness of $\Lambda_T(T\eta,\theta')$; reason: the setwise form of the Radon–Nikodym identity of the restrictions to $\mathcal F_T$; the finiteness is implicit in the printed formula
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, (E.3), p.44

import Mathlib
import Definitions.Def_ParetoDDO_Setting
import Definitions.Def_ParetoDDO_Statistic
import Definitions.Def_ParetoDDO_ExpFamily

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParetoDDO

/-- **Equation (E.3)** (Sutter, Van Parys, Kuhn, arXiv:2010.06606v4, p.44). Under Assumption 4.1, for `θ, θ' ∈ Θ` and
`η = g(θ) − g(θ')`, the restrictions of `P_θ` and `P_θ'` to `F_T` satisfy
`dP^T_θ / dP^T_θ' = exp(⟨η, T Ŝ_T⟩ − Λ_T(Tη, θ'))`, with `Λ_T(Tη, θ')` finite.

**Formalization Note** The density identity is written setwise over `A ∈ F_T`. -/
theorem eq_E_3
    {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ}
    (ξ : ℕ → Ω → Vec m) (hξ : ∀ t, Measurable (ξ t))
    (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (hP : IsAmbiguitySet P Θ)
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (hS : IsStatistic ξ P Θ Ŝ S Sinf)
    (θbar : Vec d) (g : Vec d → Vec d) (h41 : IsExpFamily ξ P Θ Ŝ θbar g)
    (θ θ' : Vec d) (hθ : θ ∈ Θ) (hθ' : θ' ∈ Θ) (T : ℕ) (hT : 1 ≤ T) :
    logMGF (P θ') (Ŝ T) ((T : ℝ) • (g θ - g θ')) ≠ ⊤ ∧
      ∀ A : Set Ω, MeasurableSet[histSigma ξ T] A →
        P θ A = ∫⁻ ω in A, ENNReal.ofReal (Real.exp (⟪g θ - g θ', (T : ℝ) • Ŝ T ω⟫ -
          (logMGF (P θ') (Ŝ T) ((T : ℝ) • (g θ - g θ'))).toReal)) ∂(P θ') := by sorry

end ParetoDDO
