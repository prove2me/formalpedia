-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_lemma_9
-- name    : RainbowEFX.Sublinear.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:36.53401+00:00
-- url     : https://prove2.me/theorems/2af99a5c-c7c3-413c-b992-3b2bb41e5280
-- title:
--   Lemma 9 (U2 [19]), p. 11 — if some agent heavily envies the pool P, there is a (1 − ε)-EFX allocation X′ >_PD X
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $0<\varepsilon<1$ and let $X$ be a $(1-\varepsilon)$-EFX allocation with pool $P$. If some agent $i$ heavily envies $P$, i.e. $v_i(X_i)<(1-\varepsilon)v_i(P)$, then there is a $(1-\varepsilon)$-EFX allocation $X'$ that strongly Pareto-dominates $X$:
--   $$
--   v_j(X'_j)\ge v_j(X_j)\ \text{ for all } j,\qquad (1-\varepsilon)\,v_{i'}(X'_{i'})>v_{i'}(X_{i'})\ \text{ for some } i'.
--   $$
--
--   Rule U2 is one of the two improving steps of the algorithm.
--
--   **Formalization Note** The paper's "in polynomial time, we can determine" is formalized as existence; running time is not formalized. Strong Pareto domination uses the strict inequality for $i'$ (see the Setting definition: the printed non-strict form is satisfied with no improvement).
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 11, Lemma 9

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem lemma_9 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (hU2 : ∃ i, HeavilyEnvies ε v X i (pool X)) :
    ∃ X' : Fin n → Finset (Fin m), IsPartialAllocation X' ∧ IsAlphaEFX (1 - ε) v X' ∧
      StronglyParetoDominates ε v X' X := by sorry

end RainbowEFX.Sublinear
