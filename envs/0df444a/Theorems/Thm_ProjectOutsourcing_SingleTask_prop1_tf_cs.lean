-- Prove2me | Theorems.Thm_ProjectOutsourcing_SingleTask_prop1_tf_cs
-- name    : ProjectOutsourcing.SingleTask.prop1_tf_cs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:06.483176+00:00
-- url     : https://prove2.me/theorems/9eaa0b2b-c600-4458-af9e-f50b3ff0e023
-- title:
--   Proposition 1 (TF, CS), p. 11, restated p. 12 — Φ^TF = Φ^CS = [0, 1], with negotiated terms (Q, −(1−θ)Π*) and (θQ, 1−θ)
-- statement:
--   Under the standing assumptions of Section 3, let $r^*$ be the system-optimal work rate and $\Pi^*=\Pi(r^*)$. Then
--
--   1. $\Phi^{TF}=[0,1]$ and $\Phi^{CS}=[0,1]$: for every bargaining power $\theta\in[0,1]$ of the subcontractor, Problem B (3) has a solution under the two-part fixed-price contract and under the cost-sharing contract, and every solution induces a system-optimal work rate;
--   2. for every $\theta\in[0,1]$, every solution of Problem B under TF has the terms
--   $$\hat p^{TF}=Q,\qquad \hat\beta^{TF}=-(1-\theta)\Pi^* ;$$
--   3. for every $\theta\in[0,1]$, every solution of Problem B under CS has the terms
--   $$\hat p^{CS}=\theta Q,\qquad \hat\beta^{CS}=1-\theta .$$
--
--   These are the two contract forms that coordinate the project for every distribution of bargaining power. The coordinating down payment of TF is nonpositive (a participation fee), and CS requires the cost to be verifiable.
--
--   **Formalization Note** "Coordinates" means that a solution exists and every solution induces the system-optimal rate. The terms are asserted for every solution, not just for one. At $\theta=0$ the CS solution makes the subcontractor indifferent among work rates; footnote 1's tie-break (he chooses the system-optimal rate) is part of the model.
-- source:
--   Hou, Lu, Deng, Shen, Coordinating Project Outsourcing through Bilateral Contract Negotiations, author manuscript (SSRN 3443865; MSOM, doi:10.1287/msom.2020.0911), p. 11, Proposition 1 (parts TF, CS); restatement p. 12

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

namespace ProjectOutsourcing.SingleTask

theorem prop1_tf_cs (M : Model) (hM : M.Valid) (rStar : ℝ) (hr : IsSystemOpt M rStar) :
    Phi M .TF = Set.Icc 0 1 ∧ Phi M .CS = Set.Icc 0 1 ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ x, IsNashSol M .TF θ x →
        x.1 = (M.Q, -(1 - θ) * sysProfit M rStar)) ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ x, IsNashSol M .CS θ x → x.1 = (θ * M.Q, 1 - θ)) := by sorry

end ProjectOutsourcing.SingleTask
