-- Prove2me | Theorems.Thm_QuantumMC_MeanEst_theorem_5
-- name    : QuantumMC.MeanEst.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:19.173672+00:00
-- url     : https://prove2.me/theorems/2136f828-6500-4191-b795-7e7c44fe29c2
-- title:
--   Theorem 5, p. 12 — Algorithm 3 has additive error ε with probability at least 2/3
-- statement:
--   Let $X=v(𝒜)$ have variance at most $\sigma^2$, where $\sigma>0$, and let $0<\epsilon<4\sigma$. Algorithm 3 samples $m$ from the law of $X/\sigma$, applies Algorithm 2 to the negative and nonnegative parts of $X/\sigma-m$ divided by four at accuracy $\epsilon/(32\sigma)$, and combines the estimates. If each Algorithm 2 run fails with probability at most $1/9$, its output $\widehat\mu$ satisfies
--
--   $$\Pr\bigl(|\widehat\mu-\mathbb E[X]|\le\epsilon\bigr)\ge\frac23.$$
--
--   The constant $D$ in Algorithm 2 may depend only on the universal Algorithm 1 constant $C$; it is chosen before the output law and accuracy. **Formalization Note** The theorem assumes $X\in L^2$ to state the variance faithfully. The quantum circuit and the asymptotic resource counts are outside this probability-space statement.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, Theorem 5 and Algorithm 3, p. 12

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

namespace QuantumMC.MeanEst

open MeasureTheory ProbabilityTheory

universe u v

/-- Theorem 5, p. 12: Algorithm 3 has additive error ϵ with probability at least 2/3. -/
theorem theorem_5 (C : ℝ) (hC : 0 < C) : ∃ D : ℝ, 0 < D ∧
  ∀ (Ω₀ : Type u) [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (X : Ω₀ → ℝ) (σ ε : ℝ), Measurable X → MemLp X 2 P₀ →
    variance X P₀ ≤ σ ^ 2 → 0 < σ → 0 < ε → ε < 4 * σ →
  ∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Ω → ℝ) (μneg μpos : Ω → ℕ → ℝ),
    Measurable m → P.map m = P₀.map (fun x => X x / σ) →
    P {ω | ¬ Alg2Succeeds C D (ε / (32 * σ)) P₀
      (alg3NegQuarter σ (m ω) X) (μneg ω)} ≤ (1 / 9 : ENNReal) →
    P {ω | ¬ Alg2Succeeds C D (ε / (32 * σ)) P₀
      (alg3PosQuarter σ (m ω) X) (μpos ω)} ≤ (1 / 9 : ENNReal) →
    (2 / 3 : ENNReal) ≤ P {ω |
      |alg3Output σ (m ω) (alg2K (ε / (32 * σ)))
        (μneg ω) (μpos ω) - ∫ x, X x ∂P₀| ≤ ε} := by sorry
end QuantumMC.MeanEst
