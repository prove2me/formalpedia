-- Prove2me | Theorems.Thm_WassTwoStage_LP1_theorem_6
-- name    : WassTwoStage.LP1.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:57:18.217361+00:00
-- url     : https://prove2.me/theorems/7de9c208-ab15-443e-9d0d-e43f4c6d0fca
-- title:
--   Theorem 6 — with $Q=0$ and $\Xi=\mathbb R^K$, the 1-Wasserstein two-stage DRO problem (1) is the linear program (32)
-- statement:
--   Consider the two-stage distributionally robust linear program (1) under the standing assumptions of Section 4 of Hanasusanto and Kuhn: the uncertainty affects only the recourse constraints ($Q = 0$), the support is $\Xi=\mathbb R^K$, the ambiguity set is the 1-Wasserstein ball of radius $\epsilon>0$ around the empirical distribution of $I\ge 1$ samples $\hat\xi_i$, with reference distance $\|\xi-\xi'\|$ for the gauge $\|\xi\| = \sum_k\max\{w_+\xi_k,-w_-\xi_k\}$, $w_+,w_->0$, and the recourse is sufficiently expensive ($\exists p\ge 0$ with $W^\top p = q$). Then:
--
--   1. for every $x\in\mathcal X$, the worst-case expectation $\mathcal Z(x)$ equals the optimal value of the linear program
--   $$\begin{aligned}\text{minimize}\quad & \epsilon\lambda + \frac1I\sum_{i\in[I]} q^\top y_i\\ \text{subject to}\quad & \lambda\in\mathbb R_+,\ y_i\in\mathbb R^{N_2}\ \forall i\in[I],\ \phi_k,\psi_k\in\mathbb R^{N_2}\ \forall k\in[K]\\ & T(x)\hat\xi_i + h(x)\le Wy_i\quad\forall i\in[I]\\ & q^\top\phi_k\le\lambda,\ q^\top\psi_k\le\lambda,\ T(x)e_k/w_+\le W\phi_k,\ -T(x)e_k/w_-\le W\psi_k\quad\forall k\in[K];\end{aligned}\qquad (32)$$
--   2. consequently the optimal value $\inf_{x\in\mathcal X} c^\top x + \mathcal Z(x)$ of problem (1) equals the optimal value of (32) minimized jointly over $x\in\mathcal X$ and the other variables, with $c^\top x$ added to the objective.
--
--   Theorem 6 is the main tractability result of Section 4: the worst-case expected recourse cost over a 1-Wasserstein ball reduces to a linear program whose size grows linearly in the number of samples and in the dimension of the uncertainty.
--
--   **Formalization Note** The printed objective of (32) omits $c^\top x$; the proof establishes the pointwise identity of item 1, and item 2 restores $c^\top x$. The hypothesis $\epsilon>0$ is not written in the paper but is required: the proof starts from Theorem 1's dual (6), stated only for $\epsilon>0$, and at $\epsilon = 0$ the identity can fail: if the dual recourse polyhedron $\{p\ge 0: W^\top p = q\}$ is unbounded in a direction $r$ with $T(x)^\top r\neq 0$, then (32) is infeasible, while $\mathcal Z(x)$ is the sample average of the recourse values, which can be finite (for instance $K=I=N_2=1$, $W=(1,-1)^\top$, $q=0$, $T(x)=(1,0)^\top$, $h(x)=0$, $\hat\xi_1=0$). All values are extended reals, so an infeasible (32) has value $+\infty$, matching $\mathcal Z(x)=+\infty$.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 22, Theorem 6 (proof pp. 23–24)

import Mathlib
import Definitions.Def_WassTwoStage_LP1_Gauge
import Definitions.Def_WassTwoStage_LP1_Setting
import Definitions.Def_WassTwoStage_LP1_Reformulations

open MeasureTheory Matrix

namespace WassTwoStage.LP1

/-- Theorem 6, Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 22 (proof pp. 23–24): under the standing
assumptions of §4 (`Q = 0`, `Ξ = ℝ^K`, 1-Wasserstein ball with the gauge (31) for `w₊, w₋ > 0`,
sufficiently expensive recourse) and `ε > 0`,
(a) for every `x ∈ X` the worst-case expectation `𝒵(x)` equals the optimal value of the linear
program (32) at that `x`; and
(b) the two-stage distributionally robust problem (1) has the same optimal value as the linear
program (32) with the first-stage cost `cᵀx` added to its objective. -/
theorem theorem_6 {K M N₁ N₂ I : ℕ} (d : Data K M N₁ N₂ I) (hI : 0 < I) (hε : 0 < d.ε)
    (hwp : 0 < d.wp) (hwm : 0 < d.wm) (hrec : d.SufficientlyExpensiveRecourse) :
    (∀ x ∈ d.X, d.worstCase x = d.lp32 x) ∧ d.value1 = d.value32 := by sorry

end WassTwoStage.LP1
