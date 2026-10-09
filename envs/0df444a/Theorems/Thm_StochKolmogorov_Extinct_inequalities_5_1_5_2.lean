-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_inequalities_5_1_5_2
-- name    : StochKolmogorov.Extinct.inequalities_5_1_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:54.540747+00:00
-- url     : https://prove2.me/theorems/732713b3-38f5-4a8f-a907-f0999c199e21
-- title:
--   §5, (5.1)–(5.2) — extinction weights and uniform margin
-- statement:
--   Suppose $\mu$ satisfies Assumption 1.3. There are positive weights $\widehat p_i<\delta_0$ for $i\in I_\mu$, a positive $\check p<\delta_0$, and $\rho_e>0$ such that every $\nu\in M_\mu\cup\{\mu\}$ satisfies
--
--   $$\sum_{j\in I_\mu}\widehat p_j\lambda_j(\nu)-\check p\max_{i\notin I_\mu}\lambda_i(\nu)>3\rho_e.$$
--
--   The margin supplies the coefficients used in Lemma 5.2 and Proposition 5.1.
--
--   **Formalization Note** The maximum inequality is written for every missing index separately. This item states the implication from Assumption 1.3 used in the paper; the cited minimax equivalence is not separately asserted.
--
--   **Moderation note** The weights may be rescaled together with the positive margin; they are chosen with $\sum_{i\in I_\mu}\widehat p_i\le\delta_0$ so that the later constant $C_U$ is finite.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §5, (5.1)–(5.2), p. 21

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem inequalities_5_1_5_2 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    ∃ phat : Fin n → ℝ, (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀ ∧
      ∃ pcheck : ℝ, 0 < pcheck ∧ pcheck < δ₀ ∧
      ∃ ρe : ℝ, 0 < ρe ∧
        ∀ ν : Measure (SDEState n), (ν ∈ subErgodic P X mu ∨ ν = mu) →
          ∀ i : Fin n, i ∉ supp mu →
            3 * ρe < (∑ j ∈ supp mu, phat j * lyap C j ν) - pcheck * lyap C i ν := by sorry

end StochKolmogorov.Extinct
