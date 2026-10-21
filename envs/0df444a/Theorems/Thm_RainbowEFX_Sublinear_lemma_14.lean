-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_lemma_14
-- name    : RainbowEFX.Sublinear.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:26.254848+00:00
-- url     : https://prove2.me/theorems/6aeea078-a906-4ab0-8f25-4ddd70ccf112
-- title:
--   Lemma 14, p. 13 — a cycle in the group champion graph meeting each V_g at most once gives a (1 − ε)-EFX allocation X′ >_PD X
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $0<\varepsilon\le1/2$, $d\in\mathbb N$, and let $X$ be a $(1-\varepsilon)$-EFX allocation satisfying assumption (\*), with a source assignment $s(\cdot)$ and the group champion graph $G$ on the parts $V_g$, $g\in L_X$ (see Observation 13). If $G$ has a directed cycle that contains at most one vertex from each $V_g$, then there is a $(1-\varepsilon)$-EFX allocation $X'$ with $X'>_{PD}X$.
--
--   Together with Theorem 3 and Observation 13 this turns a large set $L_X$ into an improving step.
--
--   **Formalization Note** The paper's "in polynomial time, we can determine" is formalized as existence; running time is not formalized. The cycle is a map $c:\{0,\dots,r-1\}\to G$ with $r\ge2$, whose vertices lie in distinct parts.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 13, Lemma 14

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem lemma_14 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (d : ℕ) (hstar : Star ε v X) (src : Fin n → Fin n) (hsrc : IsSourceAssignment v X src)
    (r : ℕ) (c : Fin r → Fin m × Fin n) (hc : ∀ i, GCVertex ε v X d src (c i))
    (hcyc : IsRainbowCycle Prod.fst (GCAdj ε v X src) c) :
    ∃ X' : Fin n → Finset (Fin m), IsPartialAllocation X' ∧ IsAlphaEFX (1 - ε) v X' ∧
      StronglyParetoDominates ε v X' X := by sorry

end RainbowEFX.Sublinear
