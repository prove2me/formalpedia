-- Prove2me | Theorems.Thm_SethiChengSS_Infinite_theorem_6_1_eq_6_9
-- name    : SethiChengSS.Infinite.theorem_6_1_eq_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:43.370506+00:00
-- url     : https://prove2.me/theorems/d2db2f4e-df58-42ab-b567-5ee8495a1a47
-- title:
--   Theorem 6.1, (6.9), p. 937 — v_{n,k} ↑ v_n, a finite solution of the DP equations (6.2) in B_1
-- statement:
--   Under the standing assumptions (2.1)–(2.2), assumption (4.2) for every period, and $0 < \alpha < 1$, let $v_n = \lim_{k\to\infty} v_{n,k}$ be the limit of the truncated values (6.4). Then
--
--   1. $v_{n,k} \uparrow v_n$ as $k \to \infty$, and $v_n$ is finite;
--   2. $v_n$ solves the dynamic programming equations
--   $$v_n(i,x) = f_n(i,x) + \inf_{u\ge0}\big\{c_n(i,u) + \alpha F_{n+1}(v_{n+1})(i,x+u)\big\}, \qquad n = 0,1,2,\dots; \tag{6.2}$$
--   3. $v_n \in B_1$ for every $n$.
--
--   This identifies the limit of value iteration as a solution of the infinite-horizon optimality equation.
--
--   **Formalization Note.** The paper states Theorem 6.1 under (2.1)–(2.2) only. Its proof (Appendix, p. 938) takes minimizers $\hat u_{n,k}$ of (6.5) and bounds them by (A.3), which divides by $c^i_n$; attainment of (6.5) needs a coercivity condition (see the companion milestone on (6.5)). Assumption (4.2), which the goal Theorem 6.2 assumes anyway, is added here.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 937, Theorem 6.1, (6.9); proof pp. 937–938

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

namespace SethiChengSS.Infinite

open Filter Topology

theorem theorem_6_1_eq_6_9 {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (h42 : Cond42 D)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ n i x, Tendsto (fun k => vTrunc D α n k i x) atTop (𝓝 (vLim D α n i x))) ∧
    (∀ n i x, vLim D α n i x < ⊤) ∧
    BellmanInf D α (fun n i x => (vLim D α n i x).toReal) ∧
    (∀ n, InB1 (fun i x => (vLim D α n i x).toReal)) := by sorry

end SethiChengSS.Infinite
