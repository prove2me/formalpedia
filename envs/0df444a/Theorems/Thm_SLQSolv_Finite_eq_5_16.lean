-- Prove2me | Theorems.Thm_SLQSolv_Finite_eq_5_16
-- name    : SLQSolv.Finite.eq_5_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:56.119775+00:00
-- url     : https://prove2.me/theorems/e3e80bb3-ccc6-47e1-800b-35717d75f619
-- title:
--   (5.16), p. 2296 — P_ε(t) ⩽ M₀(t) for t ∈ [0, T] and every ε > 0
-- statement:
--   Let (H1)–(H2) and (5.6) hold, for every $\varepsilon>0$ let $P_\varepsilon$ be the strongly regular solution of (5.7), and let $M_0$ be the solution of the Lyapunov equation (3.2),
--
--   $$
--   \dot M_0+M_0A+A^\top M_0+C^\top M_0C+Q=0,\qquad M_0(T)=G.
--   $$
--
--   Then
--
--   $$
--   P_\varepsilon(t)\le M_0(t),\qquad t\in[0,T],\ \forall\varepsilon>0.
--   $$
--
--   The matrix $M_0(t)$ represents the cost of the zero control, $J^0(t,x;0)=\langle M_0(t)x,x\rangle$, so (5.16) is the upper half of the sandwich (5.11).
--
--   **Formalization Note** The Lyapunov equation is the canonical one with feedback $\Theta=0$, in integral form. Inequalities are in the Loewner order.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §5, proof of Theorem 5.3 (Sufficiency), (5.16), p. 2296

import Mathlib
import Definitions.Def_SLQSolv_Finite_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.Finite

theorem eq_5_16 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d) (h56 : IsNonnegJ0 Bs d 0)
    (Pε : ℝ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hPε : ∀ ε > 0, IsStronglyRegular (d.addR ε) (Pε ε))
    (M0 : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hM0 : IsLyapunovSol d 0 M0) :
    ∀ ε > 0, ∀ t ≤ d.T, (M0 t - Pε ε t).PosSemidef := by sorry

end SLQSolv.Finite
