-- Prove2me | Theorems.Thm_PassiveIndexing_PriceEfficiency_theorem_3
-- name    : PassiveIndexing.PriceEfficiency.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:33.743183+00:00
-- url     : https://prove2.me/theorems/4c8d7026-a992-492b-9a4f-f19c36aced0b
-- title:
--   Theorem 3, p. 6226 — price efficiency given y under increasing market indexing
-- statement:
--   Consider the Gaussian signal economy with both indexers and nonindexers present, and let $V_x(N)=\operatorname{var}(x'v\mid y_{NI})$ for any nonindexer set $NI$ of size $N$. Increasing the number of indexers means reducing $N$.
--
--   1. If $x=c\mathbf 1$ for any real scalar $c$, then $V_x(N)$ is unchanged across all admissible nonindexer sets.
--   2. If $x$ is not a scalar multiple of $\mathbf 1$, then moving to any admissible set with fewer nonindexers strictly raises its conditional variance.
--   3. For such a nonmarket portfolio, the increase caused by one additional indexer is strictly larger at a later indexing level: if $N_1=N_2+1$ and $N_2=N_3+1$, then
--   $$
--   V_x(N_2)-V_x(N_1)<V_x(N_3)-V_x(N_2).
--   $$
--
--   This is the paper's price-efficiency dichotomy between the market portfolio and every other stock portfolio.
--
--   **Formalization Note** Conditional variance is Mathlib's conditional variance given $\sigma(y)$, with equality and inequalities asserted almost surely on the common probability space. Equation (16) identifies it with variance given prices in the paper, but equilibrium prices are outside this mission. The strict reading of “increasing rate” is used; the printed second-derivative argument has a sign slip, documented in the related milestone. Each nonindexer set satisfies $1\le |NI|<m$, so both investor types are present and the matrix inverses in the supporting formulas are genuine.
-- source:
--   Baruch & Zhang, The Distortion in Prices Due to Passive Investing, Management Science 68(8), 2022, p. 6226, Theorem 3; conditioning equivalence (16) on p. 6224; https://doi.org/10.1287/mnsc.2021.4114

import Mathlib
import Definitions.Def_PassiveIndexing_PriceEfficiency_Model

namespace PassiveIndexing.PriceEfficiency

open MeasureTheory ProbabilityTheory Matrix

/-- Theorem 3, p. 6226, with conditioning on the public statistic `y` in place of prices
as justified by (16). For a nonmarket portfolio, each added indexer raises conditional
variance, and adjacent one-indexer increments grow strictly. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (muv : EuclideanSpace ℝ (Fin n))
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (v : Ω → EuclideanSpace ℝ (Fin n))
    (eps : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hmodel : SignalModel P muv Svv See v eps)
    (x : Fin n → ℝ) :
    ((∃ c : ℝ, x = c • marketPortfolio n) →
      ∀ NI NI' : Finset (Fin m), Admissible NI → Admissible NI' →
        cv P Svv See v eps x NI =ᵐ[P] cv P Svv See v eps x NI') ∧
    ((¬ ∃ c : ℝ, x = c • marketPortfolio n) →
      ∀ NI NI' : Finset (Fin m), Admissible NI → Admissible NI' →
        NI'.card < NI.card →
          ∀ᵐ ω ∂P, cv P Svv See v eps x NI ω < cv P Svv See v eps x NI' ω) ∧
    ((¬ ∃ c : ℝ, x = c • marketPortfolio n) →
      ∀ NI₁ NI₂ NI₃ : Finset (Fin m),
        Admissible NI₁ → Admissible NI₂ → Admissible NI₃ →
        NI₁.card = NI₂.card + 1 → NI₂.card = NI₃.card + 1 →
          ∀ᵐ ω ∂P,
            cv P Svv See v eps x NI₂ ω - cv P Svv See v eps x NI₁ ω <
              cv P Svv See v eps x NI₃ ω - cv P Svv See v eps x NI₂ ω) := by sorry

end PassiveIndexing.PriceEfficiency
