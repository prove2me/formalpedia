-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_one_step_5_11_5_12
-- name    : StochKolmogorov.Extinct.one_step_5_11_5_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:35:39.593304+00:00
-- url     : https://prove2.me/theorems/ef9e0740-56d8-4c99-a410-1b85909c6816
-- title:
--   (5.11)–(5.12) — capped one-step supermartingale inequality
-- statement:
--   With the constants and contraction estimate of Proposition 5.1, cap $U_\theta$ at $\varsigma$ to form $\widetilde U_\theta$. For every interior starting state $x$,
--
--   $$\mathbb E_x\widetilde U_\theta(X(n_eT_e))\le\widetilde U_\theta(x).$$
--
--   The paper then uses the Markov property to make the sampled sequence $\widetilde U_\theta(X(kn_eT_e))$ a supermartingale. This item records its one-step inequality.
--
--   **Formalization Note** The local contraction is a hypothesis identifying the selected $\theta,T_e,\delta_e$, while the conclusion applies to every interior $x$.
--
--   **Moderation note** The hypothesis carries the integrable contraction estimate of Proposition 5.1, and the capped one-step expectation is integrable.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §5, proof of Theorem 5.1, (5.11)–(5.12), p. 23

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem one_step_5_11_5_12 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (M : ℝ) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (phat : Fin n → ℝ) (hphat : (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀)
    (pcheck : ℝ) (hpcheck : 0 < pcheck ∧ pcheck < δ₀)
    (ρe : ℝ) (hρe : 0 < ρe)
    (ne : ℕ) (hne : Hconst C c γb δ₀ < γb * ((ne : ℝ) - 1))
    (Te δe θ : ℝ) (hTe : 0 < Te) (hδe : 0 < δe) (hθ : 0 < θ ∧ θ < δ₀)
    (hcontract : ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
      ∀ x ∈ openOrthant n, l1 x ≤ M →
        (∀ i : Fin n, i ∉ supp mu → x i < δe) →
        Integrable (fun ω => Utheta c mu phat pcheck θ (X x T.toNNReal ω)) P ∧
        ∫ ω, Utheta c mu phat pcheck θ (X x T.toNNReal ω) ∂P ≤
          Real.exp (-(1 / 2) * θ * ρe * T) * Utheta c mu phat pcheck θ x) :
    ∀ x ∈ openOrthant n,
      Integrable (fun ω => Utilde c mu phat pcheck θ δe
        (X x (((ne : ℝ) * Te).toNNReal) ω)) P ∧
      ∫ ω, Utilde c mu phat pcheck θ δe (X x (((ne : ℝ) * Te).toNNReal) ω) ∂P ≤
        Utilde c mu phat pcheck θ δe x := by sorry

end StochKolmogorov.Extinct
