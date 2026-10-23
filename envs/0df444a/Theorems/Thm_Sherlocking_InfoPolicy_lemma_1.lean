-- Prove2me | Theorems.Thm_Sherlocking_InfoPolicy_lemma_1
-- name    : Sherlocking.InfoPolicy.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:21.090832+00:00
-- url     : https://prove2.me/theorems/adc5cb83-3157-4169-8e8a-611fa8e2e9a8
-- title:
--   Lemma 1, p. 14 (PDF 16) — any signal's equilibrium outcome is implemented by a binary signal
-- statement:
--   Fix parameters $K,\delta$ and a referral fee $r$. Let $X$ be any set of signal realizations with a σ-algebra, $\sigma$ an information policy (a measurable family of probability distributions $\sigma(\theta)$ on $X$), $\beta:X\to[0,1]$ a measurable platform strategy and $E$ a measurable set of entering types, such that $(\sigma,\beta,E)$ is an equilibrium at fee $r$. Then there is a binary information policy $\hat\sigma$ with realizations in $\{0,1\}$ such that $(\hat\sigma,\beta^{\mathrm{rec}},E)$ is an equilibrium at fee $r$, where $\beta^{\mathrm{rec}}(1)=1$, $\beta^{\mathrm{rec}}(0)=0$ is the obedient strategy, and every type faces the same entry probability:
--   $$\hat\sigma(\theta)(\{1\}) = \int_X\beta(x)\,d\sigma(\theta)(x)\qquad\text{for every }\theta .$$
--   So the binary signal implements the same equilibrium outcome: the same entering types, and the same probability of platform entry against each type.
--
--   This is the revelation principle of the paper: realizations can be pooled into a recommendation to enter or not.
--
--   **Formalization Note** The paper states the lemma for signals defined on $[\theta_S,1]$, presuming cutoff entry. The formal statement allows any measurable entry set $E$ and signals defined on all of $\mathbb R$, which is more general. Equilibrium is the model's weak PBE with the platform's optimality in ex-ante form (see the model definition).
-- source:
--   Choi, Kim & Mukherjee, “Sherlocking” and Platform Information Policy, CESifo Working Paper No. 10769 / SSRN 4643950 (version of November 13, 2023), p. 14 (PDF 16), Lemma 1 (proof pp. 24–25, PDF 26–27)

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

namespace Sherlocking.InfoPolicy

open MeasureTheory

theorem lemma_1 (K δ r : ℝ) {X : Type} [MeasurableSpace X] (σ : ℝ → Measure X) (β : X → ℝ) (E : Set ℝ) (hσ : IsInfoPolicy σ) (hβ : Measurable β) (hβ01 : ∀ x, β x ∈ Set.Icc (0:ℝ) 1) (hE : MeasurableSet E) (heq : IsEquilibrium K δ r σ β E) : ∃ σ' : ℝ → Measure Bool, IsInfoPolicy σ' ∧ IsEquilibrium K δ r σ' recommend E ∧ ∀ θ, entryProb σ' recommend θ = entryProb σ β θ := by sorry

end Sherlocking.InfoPolicy
