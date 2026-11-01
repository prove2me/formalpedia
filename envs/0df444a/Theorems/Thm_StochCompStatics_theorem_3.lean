-- Prove2me | Theorems.Thm_StochCompStatics_theorem_3
-- name    : StochCompStatics.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:25.512983+00:00
-- url     : https://prove2.me/theorems/909c65b5-e6da-4330-bec1-2e81e93143d1
-- title:
--   Theorem 3 — the policy function and the expected decisions $E^t$ increase in the discount factor and in a complementary payoff parameter
-- statement:
--   Let $(S,A,\Gamma,p,r,\beta)$ be a discounted dynamic program whose state space $S$ is partially ordered, with a Markov transition $p$. Suppose that Assumption 1 holds and that $\Gamma$ is ascending. For each parameter value, let $V$ and $g=\max G$ be the value and policy functions under the standing assumptions, with $g$ measurable and integrable against its state laws, and let $\mathbb E^t(g)=\int_S g\,d\mu^t$ be the expected decision in period $t$ from the initial state $s(1)$.
--
--   1. **Discount factor.** Let $0<\beta_1\le\beta_2<1$. Then
--   $$
--   g(s,\beta_2)\ge g(s,\beta_1)\ \text{ for all }s\in S,\qquad \mathbb E_2^t(g(\beta_2))\ge \mathbb E_1^t(g(\beta_1))\ \text{ for all }t\in\mathbb N\text{ and every }s(1)\in S.
--   $$
--   2. **Payoff parameter.** Let $(E,\succeq)$ be a partially ordered set, $r(s,a,c)$ a payoff depending on $c\in E$ that satisfies Assumption 1(i) for every $c$ and has increasing differences in $(a,c)$ and in $(s,c)$, and fix $0<\beta<1$. Then for all $c_2\succeq c_1$,
--   $$
--   g(s,c_2)\ge g(s,c_1)\ \text{ for all }s\in S,\qquad \mathbb E_2^t(g(c_2))\ge \mathbb E_1^t(g(c_1))\ \text{ for all }t\in\mathbb N\text{ and every }s(1)\in S.
--   $$
--
--   A more patient decision maker, or one whose payoff rewards higher actions more, chooses higher actions now and, in expectation, in every future period.
--
--   Differences from the source:
--   - generalization: state space S ⊆ ℝⁿ a Borel set with the componentwise order → any measurable space S with a partial order; reason: the paper's S with the Borel σ-algebra and the componentwise order is an instance
--   - encoding: action space A ⊆ ℝ, p and r defined on S × A → A : Set ℝ, p a Markov kernel on S × ℝ, r : S → ℝ → ℝ, every hypothesis on p and r imposed for a ∈ A only; reason: values of p and r at actions outside A are never used; same instances
--   - generalization: Γ a measurable subset of S × A with measurable sections; r measurable → not assumed; reason: no step uses these measurability conditions; every instance of the paper is covered
--   - encoding: Tf(s) = max_{a∈Γ(s)} h(s, a, f) → bellman = sSup of the image h(s, Γ(s), f), with the attainment of the maximum as a hypothesis wherever the paper writes max; reason: the paper's max presupposes attainment; sSup equals the maximum when it is attained
--   - generalization: V is the unique continuous solution of TV = V, Tⁿf → V uniformly for every f ∈ B(S), and V(s) = sup_σ V_σ(s) → StandingAssumptions: Tⁿ0 → V uniformly, V = TV with the maximum attained, the maxima along Tⁿ0 attained; continuity and uniqueness not assumed; reason: only f = 0 and the Bellman equation are used; a uniform limit is unique, so V is the paper's value function under its standing assumptions
--   - reading: footnote 9: all functions are assumed to be integrable → Tⁿ0 and V measurable and integrable against every p(s, a), a ∈ A; each policy g integrable against its own state laws µᵗ; reason: the integrals in h, T and Eᵗ are the Bochner integral, which is 0 for a non-integrable function; these are the integrals the paper writes
--   - reading: p monotone: for every increasing f, ∫ f(s′)p(s, a, ds′) is increasing in (s, a) → for every increasing measurable f integrable against every p(s, a), a ∈ A, the integral is monotone on S × A; reason: footnote 9: the integral of f exists only for such f
--   - reading: g(s) = max G(s), a policy (policies are Borel measurable, p.5) → IsPolicyFunction: g(s) is the greatest element of G(s) and g is measurable; reason: g is a stationary policy; measurability makes µᵗ the law of the controlled chain
--   - encoding: periods t ∈ ℕ = {1, 2, …}, µ¹ = δ_{s(1)} → t : ℕ starting at 0, stateLaw p g s₁ 0 = δ_{s₁}; reason: Lean index t is the paper's period t + 1; same statements
--   - encoding: (ii) r(s, a, c) has increasing differences in (a, c) and in (s, c); Assumption 1 holds → increasing differences on A × E for each s and on S × E for each a ∈ A; Assumption 1 for r(·, ·, c) for every c ∈ E; reason: the paper's parameterized program; same instances
-- source:
--   Light, Stochastic Comparative Statics in Markov Decision Processes, arXiv:1904.05481v2, Theorem 3, p.11 (proof: Appendix §6.2, pp.21–22)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn
import Definitions.Def_StochCompStatics_ChainLaw
import Definitions.Def_StochCompStatics_Model

namespace StochCompStatics

open MeasureTheory ProbabilityTheory Supermodularity.Monotonicity

universe u v

/-- Theorem 3 (Light, Stochastic Comparative Statics in Markov Decision Processes,
arXiv:1904.05481v2, §3.2, p.11): suppose that Assumption 1 holds and that `Γ(s)` is ascending.
(i) Let `0 < β₁ ≤ β₂ < 1`. Then `g(s, β₂) ≥ g(s, β₁)` for all `s ∈ S` and
`E^t_2(g(β₂)) ≥ E^t_1(g(β₁))` for all `t ∈ ℕ`.
(ii) Let `c ∈ E` be a parameter of the payoff function. If `r(s, a, c)` has increasing
differences in `(a, c)` and in `(s, c)`, then `g(s, c₂) ≥ g(s, c₁)` for all `s ∈ S`, and
`E^t_2(g(c₂)) ≥ E^t_1(g(c₁))` for all `t ∈ ℕ` whenever `c₂ ⪰ c₁`.

**Formalization Note** The state space is any measurable space with a partial order (the paper's
Borel `S ⊆ ℝⁿ` with the componentwise order is an instance); actions are reals in `A ⊆ ℝ`, and `p`
is a Markov kernel on `S × ℝ`, the same in both compared problems. `V β`, `g β` (resp. `V c`,
`g c`) are the value and policy functions of the problem with discount factor `β` (resp. payoff
parameter `c`): they satisfy the standing assumptions of p.6 (`StandingAssumptions`), `g` is the
greatest element of `G` and measurable (`IsPolicyFunction`), and `g` is integrable against its
state laws (footnote 9). `E^t_i(g)` is `expectedDecision p g s₁ t` with Lean index `t` = period
`t + 1`, for every initial state `s₁`. In (ii), Assumption 1 holds for `r(·, ·, c)` for every `c`,
increasing differences in `(a, c)` are on `A × E` for each `s`, and in `(s, c)` on `S × E` for each
`a ∈ A`. -/
theorem theorem_3 :
    (∀ {S : Type u} [MeasurableSpace S] [PartialOrder S] (A : Set ℝ) (Γ : S → Set ℝ)
      (p : Kernel (S × ℝ) S) (r : S → ℝ → ℝ) (V g : ℝ → S → ℝ),
      IsMarkovKernel p → IsActionCorr A Γ → Assumption1 A Γ p r → IsAscending Γ →
      (∀ β ∈ Set.Ioo (0 : ℝ) 1, StandingAssumptions A Γ p r β (V β) ∧
        IsPolicyFunction Γ p r β (V β) (g β) ∧
        ∀ s₁ t, Integrable (g β) (stateLaw p (g β) s₁ t)) →
      ∀ β₁ β₂ : ℝ, 0 < β₁ → β₁ ≤ β₂ → β₂ < 1 →
        (∀ s, g β₁ s ≤ g β₂ s) ∧
        ∀ s₁ t, expectedDecision p (g β₁) s₁ t ≤ expectedDecision p (g β₂) s₁ t) ∧
    (∀ {S : Type u} [MeasurableSpace S] [PartialOrder S] {E : Type v} [PartialOrder E]
      (A : Set ℝ) (Γ : S → Set ℝ) (p : Kernel (S × ℝ) S) (r : S → ℝ → E → ℝ) (β : ℝ)
      (V g : E → S → ℝ),
      IsMarkovKernel p → 0 < β → β < 1 → IsActionCorr A Γ →
      (∀ c, Assumption1 A Γ p (fun s a => r s a c)) → IsAscending Γ →
      (∀ s, IncreasingDifferencesOn (fun a c => r s a c) (A ×ˢ Set.univ)) →
      (∀ a ∈ A, IncreasingDifferencesOn (fun s c => r s a c) Set.univ) →
      (∀ c, StandingAssumptions A Γ p (fun s a => r s a c) β (V c) ∧
        IsPolicyFunction Γ p (fun s a => r s a c) β (V c) (g c) ∧
        ∀ s₁ t, Integrable (g c) (stateLaw p (g c) s₁ t)) →
      ∀ c₁ c₂ : E, c₁ ≤ c₂ →
        (∀ s, g c₁ s ≤ g c₂ s) ∧
        ∀ s₁ t, expectedDecision p (g c₁) s₁ t ≤ expectedDecision p (g c₂) s₁ t) := by sorry

end StochCompStatics
