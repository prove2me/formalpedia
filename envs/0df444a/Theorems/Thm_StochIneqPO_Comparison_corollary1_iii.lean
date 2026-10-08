-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_corollary1_iii
-- name    : StochIneqPO.Comparison.corollary1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:17:59.257796+00:00
-- url     : https://prove2.me/theorems/379a8ce2-4371-484a-beee-435634281c98
-- title:
--   Corollary 1 (iii) — $E f(X_n) \le E f(Y_n)$ for nondecreasing $f$
-- statement:
--   In the setting of Corollary 1 (i) — $E_1 = E_2 = \cdots = E$ a partially ordered Polish space, $P_1 \prec Q_1$, kernels satisfying (4), and random sequences $(X_n)$, $(Y_n)$ with the corresponding initial and conditional laws — let $f : E \to \mathbb R$ be nondecreasing and measurable. Then
--   $$E\big(f(X_n)\big) \le E\big(f(Y_n)\big)$$
--   for every $n$ for which both expectations exist.
--
--   Here $f$ need not be bounded; this extends the defining inequality of $\prec$ beyond bounded test functions.
--
--   **Formalization Note** The statement is formulated for the laws `Kernel.trajMeasure P₁ p` and `trajMeasure Q₁ q`, with 0-based coordinates. Expectations are taken in the extended sense: $E f(X_n) = E f(X_n)^+ - E f(X_n)^-$ with the two parts written as lower Lebesgue integrals `∫⁻ ENNReal.ofReal (f (x n))` and `∫⁻ ENNReal.ofReal (-f (x n))`. "The expectation exists" is the hypothesis that the two parts are not both $+\infty$ (one hypothesis for each sequence), and the conclusion compares the differences in `EReal`, so the values $\pm\infty$ are covered; under these hypotheses `EReal` subtraction never meets $\infty - \infty$.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Corollary 1 (iii), p. 904 (PDF p. 6)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory Finset

theorem corollary1_iii {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P₁ Q₁ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π _ : Iic n, E) E)
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (hPQ : StochLE P₁ Q₁)
    (hpq : ∀ n, ∀ x y : Π _ : Iic n, E, x ≤ y → StochLE (p n x) (q n y))
    (f : E → ℝ) (hf : Measurable f) (hmono : Monotone f) (n : ℕ)
    (hexP : ∫⁻ x, ENNReal.ofReal (f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) P₁ p) ≠ ⊤ ∨
      ∫⁻ x, ENNReal.ofReal (-f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) P₁ p) ≠ ⊤)
    (hexQ : ∫⁻ x, ENNReal.ofReal (f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) Q₁ q) ≠ ⊤ ∨
      ∫⁻ x, ENNReal.ofReal (-f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) Q₁ q) ≠ ⊤) :
    ((∫⁻ x, ENNReal.ofReal (f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) P₁ p) : EReal) -
        (∫⁻ x, ENNReal.ofReal (-f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) P₁ p) : EReal)) ≤
      ((∫⁻ x, ENNReal.ofReal (f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) Q₁ q) : EReal) -
        (∫⁻ x, ENNReal.ofReal (-f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) Q₁ q) : EReal)) := by sorry

end StochIneqPO.Comparison
