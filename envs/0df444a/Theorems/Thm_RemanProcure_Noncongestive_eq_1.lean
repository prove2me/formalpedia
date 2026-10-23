-- Prove2me | Theorems.Thm_RemanProcure_Noncongestive_eq_1
-- name    : RemanProcure.Noncongestive.eq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:16.953932+00:00
-- url     : https://prove2.me/theorems/ab70f7e4-254b-4a69-8ee3-f93dbbc3e645
-- title:
--   Eq. (1), p. 1444 — value iteration from 0 converges and its limit v* solves the optimality equation v* = µT1v* + λT2v* + h
-- statement:
--   In the core acquisition model (standing assumptions of §2), let $T$ be the operator $Tv=\mu T_1v+\lambda T_2v+h$ and let $v^*$ be the pointwise limit of value iteration from the zero function. Then for every state $x\in\mathbb N_0^K$ the sequence $T^n0(x)$ converges to $v^*(x)$, and $v^*$ satisfies the optimality equation
--   $$v^*(x)=\mu T_1v^*(x)+\lambda T_2v^*(x)+h(x)\qquad\text{for all }x. \tag{1}$$
--
--   This makes the optimal cost function a well-defined object solving (1); every structural statement of the mission is about this $v^*$.
--
--   **Formalization Note** The paper states (1) for the optimal discounted cost $v^*=v^{\pi^*}$ and refers to its online appendix for the derivation. Here $v^*$ is pinned down as the value-iteration limit, because with unbounded holding costs (1) alone is not known to determine $v^*$. The hypotheses are the standing assumptions, including the disclosed additions $K\ge1$, $p$ a probability vector, $r_i\ge0$, $c_A\ge0$, $\mu,\lambda>0$.
-- source:
--   Nadar, Akan, Debo & Scheller-Wolf, Optimal Procurement in Remanufacturing Systems with Uncertain Used-Item Condition, Oper. Res. 71(5) (2023), p. 1444 (PDF 5), eq. (1)

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model

namespace RemanProcure.Noncongestive
theorem eq_1 {K : ℕ} (P : Params K) (hP : Standing P) : (∀ x, Filter.Tendsto (fun n : ℕ => ((T P)^[n] 0) x) Filter.atTop (nhds (vstar P x))) ∧ (∀ x, vstar P x = P.μ * T1 P (vstar P) x + P.lam * T2 P (vstar P) x + hold P x) := by sorry
end RemanProcure.Noncongestive
