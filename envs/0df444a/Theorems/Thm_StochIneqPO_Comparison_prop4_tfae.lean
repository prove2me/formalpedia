-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_prop4_tfae
-- name    : StochIneqPO.Comparison.prop4_tfae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:17:28.870333+00:00
-- url     : https://prove2.me/theorems/027f639c-c13d-4068-81b9-6c447e43fea3
-- title:
--   Proposition 4 — $P_1 \prec P_2 \prec \cdots$ iff a.s. nondecreasing random elements with these laws exist
-- statement:
--   Let $E$ be a partially ordered Polish space and $(P_1, P_2, \dots)$ a sequence of probability measures on $E$. The following are equivalent.
--
--   1. $P_1 \prec P_2 \prec P_3 \prec \cdots$.
--   2. There are random elements $X_1, X_2, \dots$ in $E$ defined on a common probability space such that $X_1 \le X_2 \le \cdots$ almost surely and $X_i$ has law $P_i$ for every $i$.
--   3. There are a real random variable $Z$ and measurable maps $f_i : \mathbb R \to E$ with $f_1 \le f_2 \le \cdots$ (pointwise) such that $P_i$ is the law of $f_i(Z)$ for every $i$.
--
--   This extends Theorem 1 from a pair of measures to a whole chain.
--
--   **Formalization Note** The sequence is indexed from $0$. "$X_1 \le X_2 \le \cdots$ a.s." is a single almost-sure event on which $X_i \le X_{i+1}$ for all $i$. Measurability of the $f_i$ is the paper's standing convention (Sec. 1). The probability space is some `Ω : Type`.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Proposition 4, p. 907 (PDF p. 9)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory

theorem prop4_tfae {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P : ℕ → Measure E) [∀ i, IsProbabilityMeasure (P i)] :
    List.TFAE
      [ -- (i)
        ∀ i, StochLE (P i) (P (i + 1)),
        -- (ii)
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
          ∃ X : ℕ → Ω → E, (∀ i, Measurable (X i)) ∧ (∀ᵐ ω ∂μ, ∀ i, X i ω ≤ X (i + 1) ω) ∧
            ∀ i, μ.map (X i) = P i,
        -- (iii)
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
          ∃ (Z : Ω → ℝ) (f : ℕ → ℝ → E), Measurable Z ∧ (∀ i, Measurable (f i)) ∧
            (∀ i t, f i t ≤ f (i + 1) t) ∧ ∀ i, μ.map (fun ω => f i (Z ω)) = P i ] := by sorry

end StochIneqPO.Comparison
