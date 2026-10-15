-- Prove2me | Theorems.Thm_RiskPersuasion_Convex_lemma_5
-- name    : RiskPersuasion.Convex.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:58.860425+00:00
-- url     : https://prove2.me/theorems/6fc24a4e-7008-4332-9bd8-36198da27524
-- title:
--   Lemma 5 — problem (4) is equivalent to problem (14) over Bayes-plausible measures
-- statement:
--   Let $\Omega$ and $A$ be finite, $\mu^* \in \Delta(\Omega)$, $\rho$ the receiver's utility with every $P_a$ closed (Assumption 1), and $v$ the sender's utility. Fix a measurable receiver strategy $a : \Delta(\Omega) \to A$ that is optimal for belief signals, i.e. $a(s) \in \arg\max_{a'} \rho(s, a')$ for every $s \in \Delta(\Omega)$.
--
--   1. For every signaling scheme $\pi$ on $\Omega \times \Delta(\Omega)$ with $\mu_s = s$ almost surely, the signal marginal $\eta = \pi(\Omega, \cdot)$ is Bayes-plausible and
--   $$\mathbb{E}_\pi[v(\bar\omega, a(\bar s))] = \mathbb{E}_\eta\Big[\sum_{\omega \in \Omega} \bar s(\omega)\, v(\omega, a(\bar s))\Big].$$
--   2. For every Bayes-plausible $\eta$ there is a signaling scheme $\pi$ with $\mu_s = s$ almost surely, signal marginal $\eta$, and the same equality of values.
--
--   Hence the feasible values of the belief-recommendation problem (4) and of problem (14) over Bayes-plausible measures coincide, strategy by strategy.
--
--   **Formalization Note** "$\mu_s = s$" is rendered as: the identity is a version of the Bayes posterior. Assumption 1 is carried as a standing hypothesis of the paper.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 36, Lemma 5 (problem (4) on p. 15, problem (14) on p. 36)

import Mathlib
import Definitions.Def_RiskPersuasion_Convex_Program7

open MeasureTheory

namespace RiskPersuasion.Convex

theorem lemma_5 {Ω A : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype A] [Nonempty A]
    (μstar : Ω → ℝ) (hμ : μstar ∈ stdSimplex ℝ Ω) (ρ : (Ω → ℝ) → A → ℝ) (v : Ω → A → ℝ)
    (hP : ∀ a : A, IsClosed (P ρ a))
    (a : Belief Ω → A) (ha_opt : IsOptimalStrategy ρ (fun s : Belief Ω => (s : Ω → ℝ)) a)
    (ha_meas : IsMeasurableStrategy a) :
    (∀ π : Measure (Ω × Belief Ω), IsSignalingScheme μstar π →
        IsPosterior π (fun s : Belief Ω => (s : Ω → ℝ)) →
        IsBayesPlausible μstar (π.map Prod.snd) ∧
          senderValue v π a = beliefValue v (π.map Prod.snd) a) ∧
    (∀ η : Measure (Belief Ω), IsBayesPlausible μstar η →
        ∃ π : Measure (Ω × Belief Ω), IsSignalingScheme μstar π ∧
          IsPosterior π (fun s : Belief Ω => (s : Ω → ℝ)) ∧ π.map Prod.snd = η ∧
          senderValue v π a = beliefValue v η a) := by sorry

end RiskPersuasion.Convex
