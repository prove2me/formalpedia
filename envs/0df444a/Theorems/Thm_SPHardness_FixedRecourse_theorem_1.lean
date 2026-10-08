-- Prove2me | Theorems.Thm_SPHardness_FixedRecourse_theorem_1
-- name    : SPHardness.FixedRecourse.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:44.742979+00:00
-- url     : https://prove2.me/theorems/7568443f-07d0-4225-ac6b-02eab9f10735
-- title:
--   Theorem 1 with Lemma 1, pp. 4–8 — accurate recourse values recover #Parity
-- statement:
--   The reduction behind Theorem 1 converts sufficiently accurate expected-recourse values of (2) into the exact #Parity count. Let $k\ge1$, let $\alpha\in\mathbb N^k$ have positive weights, let $\beta\le\sum_j\alpha_j$, and let $0<\delta$ satisfy (7). Suppose $Q_\delta(t)$ approximates $\mathcal Q(\alpha,t)$ to within $\delta$ for every $t\ge0$. Set $h=2\sqrt\delta$, $\gamma_i=\beta+i/(k+1)$, and
--   $$\widetilde g_i=\frac{Q_\delta(\gamma_i+h)-Q_\delta(\gamma_i)}{h}+1.$$
--   For every solution $\widetilde x$ of
--   $$F\widetilde x=\left(k!\prod_{j=1}^k\alpha_j\right)\widetilde g,$$
--   one has $|\widetilde x_0-D|<1/2$. Hence rounding its first coordinate recovers the exact even-minus-odd count $D$.
--
--   The finite difference supplies the approximate knapsack volumes for Lemma 1's Vandermonde solve. The paper uses the polynomial-time cost of the other operations to infer #P-hardness.
--
--   **Formalization Note** The theorem states correctness of the reduction. Polynomial-time computability, bit lengths and the class #P are outside its Lean claim. Positive weights avoid zero denominators, $\delta>0$ makes the difference quotient defined, and $\beta\le\sum_j\alpha_j$ is the nontrivial case selected on p. 4. The oracle remains arbitrary within its error bound.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), pp. 4–8, Theorem 1 with Lemma 1, (3), (5) and (7)

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SPHardness.FixedRecourse

theorem theorem_1 {k : ℕ} (hk : 0 < k) (α : Fin k → ℕ)
    (hα : ∀ j, 1 ≤ α j) (β : ℕ) (hβ : β ≤ ∑ j, α j)
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ < delta7 (fun j => (α j : ℝ))
      (lastWeight hk (fun j => (α j : ℝ))))
    (Qδ : ℝ → ℝ)
    (hQ : ∀ t : ℝ, 0 ≤ t →
      |Qδ t - expRecourse (fun j => (α j : ℝ)) t| ≤ δ) :
    ∀ x : Fin (k + 1) → ℝ,
      (vandermondeF k (β : ℝ)).mulVec x =
        ((k.factorial : ℝ) * ∏ j, (α j : ℝ)) •
          (fun i =>
            (Qδ (budget k (β : ℝ) i + 2 * Real.sqrt δ) -
                Qδ (budget k (β : ℝ) i)) /
              (2 * Real.sqrt δ) + 1) →
        |x 0 - (parityD α β : ℝ)| < (1 / 2 : ℝ) := by sorry
end SPHardness.FixedRecourse
