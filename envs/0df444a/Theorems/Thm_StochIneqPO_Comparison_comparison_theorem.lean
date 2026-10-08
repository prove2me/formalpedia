-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_comparison_theorem
-- name    : StochIneqPO.Comparison.comparison_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:18:11.357567+00:00
-- url     : https://prove2.me/theorems/28220dcf-2021-458c-8cfc-fe8fd95ee9cd
-- title:
--   Theorem 2 — the discrete-time comparison theorem: coupled random sequences with $X_i \le Y_i$ for all $i$ a.s.
-- statement:
--   Let $E_1, E_2, \dots$ be partially ordered Polish spaces and $E^{n} = E_1 \times \cdots \times E_n$ with the coordinatewise order. Let $P_1, Q_1$ be probability measures on $E_1$, and for $n = 2, 3, \dots$ let $p_n, q_n$ be stochastic kernels from $E^{n-1}$ to $E_n$. Assume $P_1 \prec Q_1$ and
--   $$p_n(x^{n-1}, \cdot) \prec q_n(y^{n-1}, \cdot) \qquad \text{whenever } (x_1, \dots, x_{n-1}) \le (y_1, \dots, y_{n-1}). \tag{4}$$
--   Then there are random variables $X_i$, $Y_i$ with values in $E_i$, $i = 1, 2, \dots$, on a common probability space, such that $X_1 \sim P_1$, $Y_1 \sim Q_1$, the conditional distribution of $X_n$ given $X^{n-1} = x^{n-1}$ is $p_n(x^{n-1}, \cdot)$, that of $Y_n$ given $Y^{n-1} = y^{n-1}$ is $q_n(y^{n-1}, \cdot)$, and
--   $$P(X_i \le Y_i,\ i = 1, 2, \dots) = 1. \tag{5}$$
--
--   This extends O'Brien's comparison theorem (and Kalmykov's) to random sequences in partially ordered Polish spaces: two processes whose initial laws and transition kernels are ordered can be realized on one probability space so that one path dominates the other for all times simultaneously.
--
--   **Formalization Note** The initial and conditional distributions determine the joint law of $(X_1, X_2, \dots)$, which is the Ionescu-Tulcea measure; the conclusion states that the law of the whole sequence $(X_n)$ is `Kernel.trajMeasure P₁ p` and that of $(Y_n)$ is `trajMeasure Q₁ q` (equivalent to the conditional-law formulation, which holds only up to null sets). Indices are 0-based: the paper's $E_i$, $X_i$ are `E (i - 1)`, `X (i - 1)`, and the paper's kernel $p_n$ ($n \ge 2$) is `p (n - 2) : Kernel (Π i : Iic (n - 2), E i) (E (n - 1))`. Hypothesis (4) is pointwise for all ordered pairs of histories; no stochastic monotonicity of the kernels is assumed. The conclusion (5) is one almost-sure event for all indices jointly. Every $E_i$ is a *partially ordered* Polish space by the paper's standing assumption (Sec. 1), although the theorem says "Polish spaces".
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Theorem 2, eqs. (4)–(5), p. 903 (PDF p. 5)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory Finset

theorem comparison_theorem {E : ℕ → Type*} [∀ n, TopologicalSpace (E n)]
    [∀ n, PolishSpace (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]
    [∀ n, PartialOrder (E n)] [∀ n, OrderClosedTopology (E n)]
    (P₁ Q₁ : Measure (E 0)) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π i : Iic n, E i) (E (n + 1)))
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (hPQ : StochLE P₁ Q₁)
    (hpq : ∀ n, ∀ x y : Π i : Iic n, E i, x ≤ y → StochLE (p n x) (q n y)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ (X Y : (n : ℕ) → Ω → E n), (∀ n, Measurable (X n)) ∧ (∀ n, Measurable (Y n)) ∧
        μ.map (fun ω n => X n ω) = Kernel.trajMeasure P₁ p ∧
        μ.map (fun ω n => Y n ω) = Kernel.trajMeasure Q₁ q ∧
        ∀ᵐ ω ∂μ, ∀ n, X n ω ≤ Y n ω := by sorry

end StochIneqPO.Comparison
