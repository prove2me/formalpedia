-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_observation_13
-- name    : RainbowEFX.Sublinear.observation_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:08.787315+00:00
-- url     : https://prove2.me/theorems/75200def-ed87-4162-8b44-ed803d54f9f1
-- title:
--   Observation 13, p. 13 — under (*), for g, h ∈ L_X every vertex of V_h has an incoming edge from V_g in the group champion graph
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $0<\varepsilon\le1/2$, $d\in\mathbb N$, and let $X$ be a $(1-\varepsilon)$-EFX allocation satisfying assumption (\*). Fix a source assignment $s(\cdot)$ (each agent $a$ is reachable in $E_X$ from the source $s(a)$) and form the group champion graph $G$: for each low-demand good $g\in L_X$ the part $V_g=\{(g,s(a)) : a\in Q_g\}$, where $Q_g$ is the set of agents to whom $g$ is valuable, and an edge from $(g,s(a))$ to $(h,s(b))$ ($a\in Q_g$, $b\in Q_h$) iff $a$ is the champion of $X_{s(b)}\cup\{g\}$.
--
--   Then for any $g,h\in L_X$, every vertex in $V_h$ has an incoming edge from a vertex in $V_g$.
--
--   This is condition 2 of Definition 2 for $G$, which lets Theorem 3 be applied to the group champion graph.
--
--   **Formalization Note** "Champion" is read relationally as "a most envious agent".
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 13, Observation 13

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem observation_13 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (d : ℕ) (hstar : Star ε v X) (src : Fin n → Fin n) (hsrc : IsSourceAssignment v X src)
    (g h : Fin m) (hg : g ∈ LX ε v X d) (hh : h ∈ LX ε v X d) (x : Fin n)
    (hx : GCVertex ε v X d src (h, x)) :
    ∃ y, GCVertex ε v X d src (g, y) ∧ GCAdj ε v X src (g, y) (h, x) := by sorry

end RainbowEFX.Sublinear
