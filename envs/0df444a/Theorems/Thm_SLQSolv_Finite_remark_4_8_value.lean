-- Prove2me | Theorems.Thm_SLQSolv_Finite_remark_4_8_value
-- name    : SLQSolv.Finite.remark_4_8_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:30.159373+00:00
-- url     : https://prove2.me/theorems/57b1f3a9-19fd-4e50-8b57-1aef8ae037a3
-- title:
--   Remark 4.8, p. 2292 — under uniform convexity (4.2), V⁰(t, x) = ⟨P(t)x, x⟩ with P the strongly regular solution of (4.6)
-- statement:
--   Let (H1)–(H2) hold, and assume the uniform convexity condition (4.2): there is $\lambda>0$ with $J^0(0,0;u)\ge\lambda\,\mathbb E\int_0^T|u|^2ds$ for all $u\in\mathcal U[0,T]$. Let $P$ be the strongly regular solution of the Riccati equation (4.6). Then the value function of Problem (SLQ)$^0$ is
--
--   $$
--   V^0(t,x)=\langle P(t)x,x\rangle,\qquad (t,x)\in[0,T]\times\mathbb R^n.
--   $$
--
--   In Section 5 this is applied to the regularized problem with $R+\varepsilon I$, where (5.6) makes the cost uniformly convex with constant $\varepsilon$; it identifies $\langle P_\varepsilon(t)x,x\rangle$ with the regularized value $V^0_\varepsilon(t,x)$.
--
--   **Formalization Note** The equality is in $[-\infty,\infty)$ (`EReal`), so it also asserts that $V^0$ is finite. The strongly regular solution is unique under (4.2) (Theorem 4.5), so any strongly regular solution may be used. The data $b,\sigma,g,q,\rho$ need not vanish: $V^0$ is by definition the value of the homogeneous problem.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Remark 4.8, p. 2292 (under the assumptions of Corollary 4.7, p. 2291)

import Mathlib
import Definitions.Def_SLQSolv_Finite_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.Finite

theorem remark_4_8_value {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d) (h42 : IsUnifConvex Bs d 0)
    (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hP : IsStronglyRegular d P) :
    ∀ t ≤ d.T, ∀ x, V0 Bs d t x = (((P t *ᵥ x) ⬝ᵥ x : ℝ) : EReal) := by sorry

end SLQSolv.Finite
