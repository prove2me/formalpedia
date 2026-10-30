-- Prove2me | Theorems.Thm_ProjectOutsourcing_SingleTask_tb_coordinating_split
-- name    : ProjectOutsourcing.SingleTask.tb_coordinating_split
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T23:18:34.108223+00:00
-- url     : https://prove2.me/theorems/c2c34fd3-a73a-4bd9-8a18-fabf025dff95
-- title:
--   Proposition 1 (TB, only-if half) — a coordinating TB bargaining solution splits Π* as δ^TB_S(β̂) = θΠ*
-- statement:
--   Consider the single-task project of Section 3 under its standing assumptions, let $r^*$ be a system-optimal work rate, and put $\Pi^*=\Pi(r^*)$. Let $\theta\in[0,1]$ and let $x=((\hat p,\hat\beta),\hat r)$ be a solution of Problem B (3) under the time-based incentive contract TB, with payment $p\,e^{-\beta T}$ and $\beta\ge 0$. If the induced work rate $\hat r$ is system-optimal, then the subcontractor's coordinating profit equals his Nash share:
--   $$\delta^{TB}_S(\hat\beta)=\theta\,\Pi^*,\qquad \delta^{TB}_S(\beta)=\frac{\alpha Q\,\mathbb E_Z[Ze^{-\alpha Z/r^*}]\;\mathbb E_Z[e^{-(\alpha+\beta)Z/r^*}]}{(\alpha+\beta)\,\mathbb E_Z[Ze^{-(\alpha+\beta)Z/r^*}]}-c(r^*) \quad\text{(4)} .$$
--
--   This is the "only if" half of the TB part of Proposition 1: a TB bargaining solution can coordinate only if $\theta\Pi^*$ is a value of $\delta^{TB}_S$ on $[0,\infty)$. Equivalently, if $\delta^{TB}_S(\hat\beta)\neq\theta\Pi^*$, then some feasible TB outcome off $r^*$ has a strictly larger Nash product. The mechanism is to perturb $\hat p$ toward the Nash split: the gain in the Nash product is first order, and the loss of system profit is of higher order, because $\Pi'(r^*)=0$ and the subcontractor's best response moves with $p$ at a bounded rate.
--
--   **Formalization Note** At a system-optimal induced rate, the first-order condition (2) forces $\hat p$ to be the TB price of p. 11, so the subcontractor's profit is $\delta^{TB}_S(\hat\beta)$, and the client's is $\Pi^*-\delta^{TB}_S(\hat\beta)$. The claim is that this split must be the Nash split $(\theta\Pi^*,(1-\theta)\Pi^*)$. Together with the rest of the TB analysis (existence of the coordinating term when $\theta\Pi^*\in\delta^{TB}_S([0,\infty))$, continuity of $\delta^{TB}_S$, and the first-order conditions), this statement yields `ProjectOutsourcing.SingleTask.prop1_tb`. Conversely, it follows from `prop1_tb`. It isolates the perturbation step of the proof. That step needs a quantitative curvature property of $r\mapsto\mathbb E[e^{-sZ/r}]$, which is where the strict concavity of $F$ (Assumption 1) enters. The standing assumptions are the hypotheses.
-- source:
--   Hou, Lu, Deng, Shen, Coordinating Project Outsourcing through Bilateral Contract Negotiations, author manuscript (SSRN 3443865; MSOM, doi:10.1287/msom.2020.0911), p. 11, Proposition 1 (TB part) and (4); restatement p. 12

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

namespace ProjectOutsourcing.SingleTask

theorem tb_coordinating_split (M : Model) (hM : M.Valid) (rStar : ℝ) (hr : IsSystemOpt M rStar) :
    ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ x, IsNashSol M .TB θ x → IsSystemOpt M x.2 →
      deltaTB M rStar x.1.2 = θ * sysProfit M rStar := by sorry

end ProjectOutsourcing.SingleTask
