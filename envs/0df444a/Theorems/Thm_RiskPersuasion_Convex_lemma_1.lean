-- Prove2me | Theorems.Thm_RiskPersuasion_Convex_lemma_1
-- name    : RiskPersuasion.Convex.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:56.206847+00:00
-- url     : https://prove2.me/theorems/cfd65ac6-9195-4958-9bc7-1552047e7bd5
-- title:
--   Lemma 1 — schemes with belief signals ↔ Bayes-plausible measures (Aumann–Maschler, Kamenica–Gentzkow)
-- statement:
--   Let $\Omega$ be a finite state space and $\mu^* \in \Delta(\Omega)$ a prior. Consider signaling schemes whose signals are beliefs, i.e. probability measures $\pi$ on $\Omega \times \Delta(\Omega)$ with $\Omega$-marginal $\mu^*$.
--
--   1. If the receiver's posterior after signal $s$ equals $s$ for $\pi$-almost every signal ($\mu_s = s$ a.s.), then the signal marginal $\eta(\cdot) = \pi(\Omega, \cdot)$ is Bayes-plausible:
--   $$\mathbb{E}_\eta[\bar s(\omega)] = \mu^*(\omega) \quad \text{for every } \omega \in \Omega.$$
--   2. Conversely, let $\eta$ be a Bayes-plausible probability measure on $\Delta(\Omega)$. There is a measure $\pi$ on $\Omega \times \Delta(\Omega)$ with $\pi(\omega, ds) = s(\omega)\,\eta(ds)$, i.e. $\pi(\{\omega\} \times B) = \int_B s(\omega)\,\eta(ds)$ for every measurable $B$; and every such $\pi$ is a signaling scheme for $\mu^*$ under which $\mu_s = s$ is a version of the posterior.
--
--   This is the splitting lemma: belief-recommendation schemes correspond exactly to distributions of posteriors whose mean is the prior.
--
--   **Formalization Note** "$\mu_s = s$ for almost all $s$" is rendered as: the identity map is a version of the Bayes posterior under $\pi$. The paper's converse says "$\mu_s = s$ for all $s$", but its proof (p. 36) establishes it $\eta$-almost surely, which is all a posterior can satisfy; the a.e. form is stated.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 15, Lemma 1 (proof pp. 35–36)

import Mathlib
import Definitions.Def_RiskPersuasion_Convex_Program7

open MeasureTheory

namespace RiskPersuasion.Convex

theorem lemma_1 {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μstar : Ω → ℝ) (hμ : μstar ∈ stdSimplex ℝ Ω) :
    (∀ π : Measure (Ω × Belief Ω), IsSignalingScheme μstar π →
        IsPosterior π (fun s : Belief Ω => (s : Ω → ℝ)) → IsBayesPlausible μstar (π.map Prod.snd)) ∧
    (∀ η : Measure (Belief Ω), IsBayesPlausible μstar η →
        (∃ π : Measure (Ω × Belief Ω), ∀ (ω : Ω) (B : Set (Belief Ω)), MeasurableSet B →
            π ({ω} ×ˢ B) = ENNReal.ofReal (∫ s in B, (s : Ω → ℝ) ω ∂η)) ∧
        ∀ π : Measure (Ω × Belief Ω),
          (∀ (ω : Ω) (B : Set (Belief Ω)), MeasurableSet B →
            π ({ω} ×ˢ B) = ENNReal.ofReal (∫ s in B, (s : Ω → ℝ) ω ∂η)) →
          IsSignalingScheme μstar π ∧ IsPosterior π (fun s : Belief Ω => (s : Ω → ℝ))) := by sorry

end RiskPersuasion.Convex
