-- Prove2me | Theorems.Thm_RobustUncLP_WorstCase_exists_infeasible_instance_of_11
-- name    : RobustUncLP.WorstCase.exists_infeasible_instance_of_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T05:52:15.80646+00:00
-- url     : https://prove2.me/theorems/184e8365-7a0d-4329-9b48-92b4dc448f3c
-- title:
--   §2.2, proof of Proposition 2.1, p. 5 — the rows averaged with the multipliers of (11) form an infeasible instance in 𝒰
-- statement:
--   Let $\mathcal U$ be a convex set of real $m\times n$ matrices with constraint-wise uncertainty, $\mathcal U = \mathcal U_1\times\dots\times\mathcal U_m$, and let $f\in\mathbb R^n$. Let $N\ge 1$, $A_1,\dots,A_N\in\mathcal U$ with rows $a_i^p$ (the $i$-th row of $A_p$), and suppose nonnegative $\lambda_{ip}$ and a real $\mu$ satisfy
--   $$\sum_{i=1}^{m}\sum_{p=1}^{N}\lambda_{ip}\,a_i^{p} + \mu f = 0,\qquad \mu > 0. \tag{11}$$
--   Then some instance is infeasible: there is $A\in\mathcal U$ such that no $x$ satisfies $Ax\ge 0$, $f^{T}x = 1$.
--
--   In the paper the instance is built explicitly: with $\lambda_i = \sum_{p}\lambda_{ip}$, its $i$-th row is $a_i = \lambda_i^{-1}\sum_p \lambda_{ip}a_i^p$ when $\lambda_i \neq 0$ and $a_i = a_i^1$ otherwise. This is the last step of the "only if" part of Proposition 2.1(i).
--
--   **Formalization Note** Only the convexity of $\mathcal U$ from the standing assumption of §2.1 is assumed here (closedness is not needed for this step). $N\ge1$ is the paper's tacit assumption that at least one instance occurs.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, p. 5, §2.2, proof of Proposition 2.1, after (11)

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting
open Matrix

namespace RobustUncLP.WorstCase

theorem exists_infeasible_instance_of_11 {m n N : ℕ}
    (U : Set (Matrix (Fin m) (Fin n) ℝ)) (f : Fin n → ℝ)
    (hconv : Convex ℝ U) (hcw : IsConstraintWise U)
    (hN : 0 < N) (A : Fin N → Matrix (Fin m) (Fin n) ℝ) (hA : ∀ p, A p ∈ U)
    (lam : Fin m → Fin N → ℝ) (μ : ℝ) (hlam : ∀ i p, 0 ≤ lam i p) (hμ : 0 < μ)
    (h11 : (∑ i, ∑ p, lam i p • A p i) + μ • f = 0) :
    ∃ A' ∈ U, instFeas f A' = ∅ := by sorry

end RobustUncLP.WorstCase
