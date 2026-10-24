-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_theorem_2
-- name    : SampleDrivenOS.Structure.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:29.121796+00:00
-- url     : https://prove2.me/theorems/fb6cec4a-9d77-440d-9463-e7b894b734d0
-- title:
--   Theorem 2 — every feasible solution of CLP$_p$ is dominated, for every $F_k$, by a feasible threshold solution of the form (7)
-- statement:
--   Fix $p\in[0,1)$ and let $q$ be a feasible solution of the continuous linear program CLP$_p$: $q(t,\ell)\ge0$, each $q(\cdot,\ell)$ is integrable on $[p,1]$, and
--   $$t\,q(t,\ell)+\int_p^t\sum_{s\ge1}q(\tau,s)\,d\tau\le1\qquad\forall t\in[p,1],\ \forall\ell\ge1 .$$
--   Then there exist another feasible solution $q^*$ and a non-decreasing sequence $(t_i)_{i\ge0}\subseteq[p,1]$ with $t_0=p$ such that
--   1. $F_k(q^*)\ge F_k(q)$ for all $k\ge1$, where $F_k(q)=\sum_{\ell=1}^{k}\int_p^1 q(t,\ell)\sum_{j=\ell}^{k}\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^{\ell}\,dt$;
--   2. for every $\ell\ge1$ and $t\in[p,1)$,
--   $$t\,q^*(t,\ell)+\int_p^t\sum_{s\ge1}q^*(\tau,s)\,d\tau=1\ \text{ if }t\ge t_\ell,\tag{5}$$
--   $$q^*(t,\ell)=0\ \text{ if }t<t_\ell;\tag{6}$$
--   3. for every $\ell\ge1$ and $t\in[p,1)$, with $T_i=\prod_{j=1}^{i}t_j$,
--   $$q^*(t,\ell)=\begin{cases}T_i/t^{i+1}&\text{if }t\in[t_i,t_{i+1}),\ \ell\le i,\\0&\text{else.}\end{cases}\tag{7}$$
--
--   Since the objective of CLP$_p$ is $Y_1-\sum_{k\ge1}(Y_k-Y_{k+1})(1-F_k(q))$ with $Y_k-Y_{k+1}\ge0$, the theorem reduces CLP$_p$ to an optimization over non-decreasing threshold sequences, the reduced problem RP$_p$ on which the rest of the paper's analysis rests.
--
--   **Formalization Note** Ranks are $\ell\ge1$ (the page's "for all $\ell\in\mathbb N$"). Equations (5)–(7) are asserted on $[p,1)$, not on $[p,1]$: $q^*$ is an element of $L^1$, so its value at $t=1$ is not determined, and as printed (5) and (7) contradict each other at $t=1$ whenever finitely many thresholds are below $1$ (e.g. $q=0$, whose improvement has all $t_\ell=1$: (7) gives $q^*(1,\ell)=0$ while (5) would need $q^*(1,\ell)=1$). Feasibility of $q^*$ still holds on all of $[p,1]$. The cumulative mass is the extended-real lower integral of the series. Dropping (5)–(7) would make the statement trivial ($q^*=q$); they are part of the conclusion.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 8 (PDF p. 9), Theorem 2, eqs. (5)–(7)

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory Set

namespace SampleDrivenOS.Structure

theorem theorem_2 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (q : ℝ → ℕ → ℝ) (hq : IsFeasible p q) :
    ∃ qstar : ℝ → ℕ → ℝ, ∃ t : ℕ → ℝ,
      IsFeasible p qstar ∧
      (∀ k : ℕ, 1 ≤ k → Fk p q k ≤ Fk p qstar k) ∧
      Monotone t ∧ t 0 = p ∧ (∀ i : ℕ, t i ∈ Icc p 1) ∧
      SolvesEq5Eq6 p t qstar ∧
      IsThresholdForm p t qstar := by sorry

end SampleDrivenOS.Structure
