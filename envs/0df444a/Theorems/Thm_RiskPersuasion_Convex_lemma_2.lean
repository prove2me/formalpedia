-- Prove2me | Theorems.Thm_RiskPersuasion_Convex_lemma_2
-- name    : RiskPersuasion.Convex.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:42.974817+00:00
-- url     : https://prove2.me/theorems/64871849-bdbe-49fd-9474-b1b4d8ef4fb2
-- title:
--   Lemma 2 — Bayes-plausible measures and mean-posteriors (b_a, m_a), Eqs. (5)–(6)
-- statement:
--   Let $\Omega$ and $A$ be finite, $\mu^* \in \Delta(\Omega)$, $\rho$ the receiver's utility with every $P_a$ closed (Assumption 1), and $v$ the sender's utility.
--
--   1. For every Bayes-plausible probability measure $\eta$ on $\Delta(\Omega)$ and every measurable optimal receiver strategy $a(\cdot)$ ($s \in P_{a(s)}$ for all $s \in \Delta(\Omega)$) there are $b_a \in [0,1]$ and $m_a \in \mathbb{R}^{\Omega}$, $a \in A$, such that $m_a \in \operatorname{Conv}(P_a)$ for every $a$ with $P_a \neq \emptyset$ (and $b_a = 0$ when $P_a = \emptyset$), and
--   $$\sum_{a \in A} b_a m_a = \mu^*, \qquad (5)$$
--   $$\mathbb{E}_\eta[\bar s(\omega)\, v(\omega, a(\bar s))] = \sum_{a \in A} b_a m_a(\omega)\, v(\omega, a) \quad \text{for each } \omega \in \Omega. \qquad (6)$$
--   2. Conversely, for all $b_a \in [0,1]$ and $m_a \in \operatorname{Conv}(P_a)$, $a \in A$, satisfying (5), there are a Bayes-plausible $\eta$ and a measurable optimal mixed receiver strategy $\sigma$ such that, for each $\omega$,
--   $$\mathbb{E}_\eta\Big[\bar s(\omega) \sum_{a \in A} \sigma(\bar s)(a)\, v(\omega, a)\Big] = \sum_{a \in A} b_a m_a(\omega)\, v(\omega, a).$$
--
--   Here $b_a$ is the probability that the receiver plays $a$ and $m_a$ is the mean posterior given that she plays $a$. The lemma replaces optimization over measures on $\Delta(\Omega)$ by optimization over finitely many vectors.
--
--   **Formalization Note** Two corrections to the printed statement. (i) If some $P_a$ is empty (an action optimal at no belief), $\operatorname{Conv}(P_a) = \emptyset$ and the printed forward direction cannot hold; the statement allows $m_a$ arbitrary in that case, where necessarily $b_a = 0$. (ii) With pure strategies the printed converse is false: with one state, two actions optimal everywhere, $v = 0$ for one and $1$ for the other, and $b = (1/2, 1/2)$, every $\eta$ is the point mass at the only belief, and a pure strategy yields $0$ or $1$, never $1/2$. The converse is stated with mixed strategies, which the paper allows (p. 11) and which its construction needs when two actions share a support point.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 16, Lemma 2, Eqs. (5)–(6) (proof pp. 36–38)

import Mathlib
import Definitions.Def_RiskPersuasion_Convex_Program7

open MeasureTheory

namespace RiskPersuasion.Convex

theorem lemma_2 {Ω A : Type} [Fintype Ω] [Fintype A] [Nonempty A]
    (μstar : Ω → ℝ) (hμ : μstar ∈ stdSimplex ℝ Ω) (ρ : (Ω → ℝ) → A → ℝ) (v : Ω → A → ℝ)
    (hP : ∀ a : A, IsClosed (P ρ a)) :
    (∀ (η : Measure (Belief Ω)) (a : Belief Ω → A), IsBayesPlausible μstar η →
        IsOptimalStrategy ρ (fun s : Belief Ω => (s : Ω → ℝ)) a → IsMeasurableStrategy a →
        ∃ (b : A → ℝ) (m : A → Ω → ℝ),
          (∀ x : A, b x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ x : A, m x ∈ convexHull ℝ (P ρ x) ∨ (b x = 0 ∧ P ρ x = ∅)) ∧
          ∑ x, b x • m x = μstar ∧
          ∀ ω : Ω, ∫ s, (s : Ω → ℝ) ω * v ω (a s) ∂η = ∑ x, b x * m x ω * v ω x) ∧
    (∀ (b : A → ℝ) (m : A → Ω → ℝ), (∀ x : A, b x ∈ Set.Icc (0 : ℝ) 1) →
        (∀ x : A, m x ∈ convexHull ℝ (P ρ x)) → ∑ x, b x • m x = μstar →
        ∃ (η : Measure (Belief Ω)) (σ : Belief Ω → A → ℝ), IsBayesPlausible μstar η ∧
          IsOptimalMixedStrategy ρ (fun s : Belief Ω => (s : Ω → ℝ)) σ ∧
          (∀ x : A, Measurable fun s => σ s x) ∧
          ∀ ω : Ω, ∫ s, (s : Ω → ℝ) ω * ∑ x, σ s x * v ω x ∂η = ∑ x, b x * m x ω * v ω x) := by sorry

end RiskPersuasion.Convex
