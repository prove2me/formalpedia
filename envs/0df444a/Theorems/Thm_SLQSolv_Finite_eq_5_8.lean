-- Prove2me | Theorems.Thm_SLQSolv_Finite_eq_5_8
-- name    : SLQSolv.Finite.eq_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:35.199492+00:00
-- url     : https://prove2.me/theorems/2e367618-09de-44e5-9ab8-ef8b2101a7d4
-- title:
--   (5.8), p. 2295 — under (5.6), the strongly regular solution P_ε of (5.7) satisfies R + εI + DᵀP_εD ⩾ εI a.e.
-- statement:
--   Let (H1)–(H2) and (5.6) hold, let $\varepsilon>0$, and let $P_\varepsilon$ be a strongly regular solution of the regularized Riccati equation (5.7) (the Riccati equation (4.6) with $R$ replaced by $R+\varepsilon I$). Then
--
--   $$
--   R(t)+\varepsilon I+D(t)^\top P_\varepsilon(t)D(t)\ \ge\ \varepsilon I\qquad\text{a.e. }t\in[0,T].
--   $$
--
--   Under (5.6) the regularized cost is uniformly convex with constant $\varepsilon$, and the strongly regular solution inherits that constant (Remark 4.6). This uniform lower bound passes to the limit $\varepsilon\to0$ and gives (5.10).
--
--   **Formalization Note** The inequality is in the Loewner order. The strongly regular solution of (5.7) is unique, so the statement is about the $P_\varepsilon$ of the paper.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §5, (5.8), p. 2295

import Mathlib
import Definitions.Def_SLQSolv_Finite_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.Finite

theorem eq_5_8 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d) (h56 : IsNonnegJ0 Bs d 0)
    (ε : ℝ) (hε : 0 < ε) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (hP : IsStronglyRegular (d.addR ε) P) :
    ∀ᵐ s ∂(volume.restrict (Icc (0:ℝ) d.T)),
      (sigmaR (d.addR ε) P s.toNNReal - ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by sorry

end SLQSolv.Finite
