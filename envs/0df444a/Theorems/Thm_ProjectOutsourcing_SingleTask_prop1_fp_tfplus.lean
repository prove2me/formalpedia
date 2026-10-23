-- Prove2me | Theorems.Thm_ProjectOutsourcing_SingleTask_prop1_fp_tfplus
-- name    : ProjectOutsourcing.SingleTask.prop1_fp_tfplus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:09.253424+00:00
-- url     : https://prove2.me/theorems/c4f8a7e3-bf3e-43f2-842f-5843a3037fec
-- title:
--   Proposition 1 (FP, TF+), p. 11, restated p. 12 — Φ^FP = Φ^TF+ = {1}, negotiated terms p = Q (and β = 0), and no coordinating solution for θ < 1
-- statement:
--   Under the standing assumptions of Section 3,
--
--   1. $\Phi^{FP}=\Phi^{TF+}=\{1\}$: the fixed-price contract and the two-part fixed-price contract with nonnegative down payment coordinate the system exactly when the subcontractor has full bargaining power $\theta=1$;
--   2. at $\theta=1$ every solution of Problem B (3) under FP has $\hat p^{FP}=Q$, and every solution under TF+ has $\hat p^{TF+}=Q$, $\hat\beta^{TF+}=0$;
--   3. for every $\theta\in[0,1)$, no solution of Problem B under FP or under TF+ induces a system-optimal work rate.
--
--   Item 3 is the strong form of "fails to coordinate": it is not only that some solution misses $r^*$, but that every solution does.
--
--   **Formalization Note** The fixed-price contract's second coordinate is a dummy fixed at $0$. "Coordinates" means that a solution exists and every solution induces the system-optimal rate.
-- source:
--   Hou, Lu, Deng, Shen, Coordinating Project Outsourcing through Bilateral Contract Negotiations, author manuscript (SSRN 3443865; MSOM, doi:10.1287/msom.2020.0911), p. 11, Proposition 1 (parts FP, TF+); restatement p. 12

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

namespace ProjectOutsourcing.SingleTask

theorem prop1_fp_tfplus (M : Model) (hM : M.Valid) :
    Phi M .FP = {1} ∧ Phi M .TFplus = {1} ∧
      (∀ x, IsNashSol M .FP 1 x → x.1.1 = M.Q) ∧
      (∀ x, IsNashSol M .TFplus 1 x → x.1 = (M.Q, 0)) ∧
      (∀ θ ∈ Set.Ico (0 : ℝ) 1, ∀ x, IsNashSol M .FP θ x → ¬ IsSystemOpt M x.2) ∧
      (∀ θ ∈ Set.Ico (0 : ℝ) 1, ∀ x, IsNashSol M .TFplus θ x → ¬ IsSystemOpt M x.2) := by sorry

end ProjectOutsourcing.SingleTask
