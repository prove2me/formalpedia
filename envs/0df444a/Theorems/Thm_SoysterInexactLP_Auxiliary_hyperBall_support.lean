-- Prove2me | Theorems.Thm_SoysterInexactLP_Auxiliary_hyperBall_support
-- name    : SoysterInexactLP.Auxiliary.hyperBall_support
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:31.571997+00:00
-- url     : https://prove2.me/theorems/e31f1e51-0ed8-4746-82a2-03c7b5fe9cb7
-- title:
--   Hypersphere activity sets: sup_{aⱼ∈Kⱼ} eᵢ·aⱼ = aᵢⱼ + ρⱼ, so āⱼ = aⱼ + ρⱼ·e
-- statement:
--   Let $A_0=(a_1,\dots,a_n)$ be an $m\times n$ matrix and $\rho_1,\dots,\rho_n\ge0$. For the Euclidean balls $K_j=\{a\in\mathbb R^m\mid\|a-a_j\|_2\le\rho_j\}$,
--   $$\delta^*(e_i\mid K_j)=\sup_{a\in K_j}a_i=a_{ij}+\rho_j\qquad\text{for all }i,j,$$
--   that is, $\bar a_j=a_j+\rho_j e$ with $e$ the vector of all ones, so $\bar A=A_0+(\rho_j)_{i,j}$.
--
--   This computes the auxiliary linear program explicitly in the paper's inexact linear programming application.
--
--   **Formalization Note** The radii are assumed nonnegative (a "magnitude"); a negative radius would give an empty set. The norm is Euclidean.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), p. 1157 (PDF p. 5), §Inexact Linear Programming, second paragraph

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

theorem hyperBall_support {m n : ℕ} (A₀ : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin n → ℝ) (hρ : ∀ j, 0 ≤ ρ j) :
    (∀ i j, supportFun (hyperBall A₀ ρ j) (Pi.single i 1) = ((A₀ i j + ρ j : ℝ) : EReal)) ∧
      Abar (hyperBall A₀ ρ) = A₀ + Matrix.of (fun _ j => ρ j) := by sorry

end SoysterInexactLP.Auxiliary
