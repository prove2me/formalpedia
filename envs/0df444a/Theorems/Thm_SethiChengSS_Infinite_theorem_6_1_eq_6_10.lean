-- Prove2me | Theorems.Thm_SethiChengSS_Infinite_theorem_6_1_eq_6_10
-- name    : SethiChengSS.Infinite.theorem_6_1_eq_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:37.482491+00:00
-- url     : https://prove2.me/theorems/a0ae707e-8386-4117-9028-4b7e913ce68f
-- title:
--   Theorem 6.1, (6.10), p. 937 — v_n ∈ C_1, a B_0 minimizer of (6.2) exists, and its feedback policy is optimal: v_n = min J_n = J_n(Û)
-- statement:
--   Under the standing assumptions (2.1)–(2.2), assumption (4.2) for every period, and $0 < \alpha < 1$, let $v_n = \lim_k v_{n,k}$. Then
--
--   1. $v_n \in C_1$ for every $n$;
--   2. there is a rule $\hat u_n(i,x) \ge 0$ in $B_0$ attaining the infimum in (6.2) at every $n$, $i$, $x$;
--   3. for every such rule $\hat U = \{\hat u_n, \hat u_{n+1}, \dots\}$, its feedback policy (3.3) started at period $n$ from surplus $x$ is admissible, $v_n$ is the value function of the infinite-horizon problem, and $\hat U$ is optimal:
--   $$v_n(i,x) = \min_{U\in\mathcal U} J_n(i,x;U) = J_n(i,x;\hat U). \tag{6.10}$$
--
--   This is the existence and verification half of the infinite-horizon theory: an optimal Markov policy is obtained from the optimality equation, and it is optimal among all history-dependent policies.
--
--   **Formalization Note.** The paper assumes only (2.1)–(2.2). Without a coercivity condition the infimum in (6.2) need not be attained, and the paper's construction of the minimizer goes through the bound (A.3), which divides by $c^i_n$; (4.2), assumed by Theorem 6.2, is added. The comparison class $\mathcal U$ is every admissible history-dependent policy.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 937, Theorem 6.1, last two sentences and (6.10); proof p. 938

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

namespace SethiChengSS.Infinite

theorem theorem_6_1_eq_6_10 {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (h42 : Cond42 D)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ n, InC1 (fun i x => (vLim D α n i x).toReal)) ∧
    (∃ û : ℕ → Fin L → ℝ → ℝ, (∀ n, InB0 (û n)) ∧
      AttainsInf D α (fun n i x => (vLim D α n i x).toReal) û) ∧
    ∀ û : ℕ → Fin L → ℝ → ℝ, (∀ n, InB0 (û n)) →
      AttainsInf D α (fun n i x => (vLim D α n i x).toReal) û →
      ∀ n i x, Admissible (feedback û n x) ∧ value D α n i x = vLim D α n i x ∧
        Jinf D α n i x (feedback û n x) = value D α n i x := by sorry

end SethiChengSS.Infinite
