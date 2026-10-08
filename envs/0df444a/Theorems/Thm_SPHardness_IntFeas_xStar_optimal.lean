-- Prove2me | Theorems.Thm_SPHardness_IntFeas_xStar_optimal
-- name    : SPHardness.IntFeas.xStar_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:39.480994+00:00
-- url     : https://prove2.me/theorems/f558968d-d4c6-4a8a-9523-acdadf0d1001
-- title:
--   Proof of Theorem 4, p. 13 — x⋆ = max{Σᵢ max{ξᵢ, 1 − ξᵢ} : Aξ ≤ b} is the unique optimal decision of (11)
-- statement:
--   Let $(A,b)$ be an instance of the Integer Feasibility Problem, so $\{y\in\mathbb R^n:Ay\le b\}\subseteq[0,1]^n$, and assume the polytope $\{\xi\in\mathbb R^n : A\xi\le b\}$ is nonempty. Let
--   $$x^\star=\max\Big\{\sum_{i=1}^n\max\{\xi_i,1-\xi_i\} : A\xi\le b\Big\}.$$
--   Then
--   1. a decision $x$ is feasible for problem (11) if and only if $x\ge x^\star$;
--   2. $x^\star$ attains the optimal value: $x^\star+\mathbb E[Q(x^\star,\tilde\xi)]=f^\star$;
--   3. $x^\star$ is the only feasible decision attaining $f^\star$.
--
--   The optimal decision of the stochastic program thus encodes the largest value of a separable function over the IFP polytope, which is how the program carries the combinatorial information of the instance.
--
--   **Formalization Note.** Feasibility of $x$ in (11) is robust: the second stage must be feasible for every $\xi\in[0,1]^n$. Under an almost-sure reading of feasibility the statement fails when the polytope is Lebesgue-null (every $x\ge0$ would then be feasible), so the robust reading is the one under which the page's claim holds. The page's $\sum_{i=1}^m$ is read as $\sum_{i=1}^n$. The nonemptiness of the polytope is the page's own assumption ("Assuming that $\{\xi\in\mathbb R^n : A\xi\le b\}\ne\emptyset$").
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), §3, proof of Theorem 4, p. 13

import Mathlib
import Definitions.Def_SPHardness_IntFeas_Model

open MeasureTheory

namespace SPHardness.IntFeas

theorem xStar_optimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) :
    (∀ x, FirstStageFeasible A b x ↔ xStar A b ≤ x) ∧
    objective A b (xStar A b) = optValue A b ∧
    ∀ x, FirstStageFeasible A b x → objective A b x = optValue A b → x = xStar A b := by sorry

end SPHardness.IntFeas
