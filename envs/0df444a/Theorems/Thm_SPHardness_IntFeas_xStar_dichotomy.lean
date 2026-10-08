-- Prove2me | Theorems.Thm_SPHardness_IntFeas_xStar_dichotomy
-- name    : SPHardness.IntFeas.xStar_dichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:43.832409+00:00
-- url     : https://prove2.me/theorems/b930ff64-800b-46b4-bb43-8688e1c28f3b
-- title:
--   Proof of Theorem 4, p. 13 — the IFP answer is yes iff x⋆ = n, and no iff x⋆ < n − ϵ′
-- statement:
--   Let $(A,b)$ be an instance of the Integer Feasibility Problem with a nonempty polytope $\{\xi\in\mathbb R^n:A\xi\le b\}$, let $x^\star=\max\{\sum_{i=1}^n\max\{\xi_i,1-\xi_i\}:A\xi\le b\}$, and let $\epsilon'$ satisfy the hypotheses of Lemma 4: $0\le\epsilon'<\tfrac12$ and $\epsilon'\sum_j|A_{ij}|<1$ for every row $i$. Then
--   $$\text{the answer is affirmative}\iff x^\star=n,\qquad \text{the answer is negative}\iff x^\star<n-\epsilon' .$$
--
--   The optimal decision of (11) therefore has a gap of width $\epsilon'$ between yes-instances and no-instances, which an approximately optimal decision can detect.
--
--   **Formalization Note.** $n$ is cast to $\mathbb R$. The condition on $\epsilon'$ is encoded as in Lemma 4 (zero rows impose nothing).
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), §3, proof of Theorem 4, p. 13

import Mathlib
import Definitions.Def_SPHardness_IntFeas_Model

open MeasureTheory

namespace SPHardness.IntFeas

theorem xStar_dichotomy {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ)
    (ε' : ℝ) (hε'0 : 0 ≤ ε') (hε'half : ε' < 1 / 2)
    (hε'row : ∀ i, ε' * ∑ j, |(A i j : ℝ)| < 1) :
    (IFPAnswer A b ↔ xStar A b = n) ∧ (¬ IFPAnswer A b ↔ xStar A b < n - ε') := by sorry

end SPHardness.IntFeas
