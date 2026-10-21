-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_lemma_10
-- name    : RainbowEFX.Sublinear.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:07.519091+00:00
-- url     : https://prove2.me/theorems/cae8e1bb-2ba6-4844-8f01-3b1b801b2ed8
-- title:
--   Lemma 10 (U3 [19]), p. 11 — sources s_i, goods g_i, agents t_i with t_i reachable from s_i and t_i the champion of X_{s_{i+1}} ∪ g_{i+1} give X′ >_PD X
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $0<\varepsilon<1$ and let $X$ be a $(1-\varepsilon)$-EFX allocation. Suppose there are $\ell\ge1$ distinct sources $s_1,\dots,s_\ell$ of the envy graph $E_X$, distinct unallocated goods $g_1,\dots,g_\ell$ and distinct agents $t_1,\dots,t_\ell$ such that, for every $i$ (indices modulo $\ell$),
--
--   1. $t_i$ is reachable from $s_i$ in $E_X$, and
--   2. $t_i$ is a champion (most envious agent) of $X_{s_{i+1}}\cup\{g_{i+1}\}$.
--
--   Then there is a $(1-\varepsilon)$-EFX allocation $X'$ with $X'>_{PD}X$.
--
--   Rule U3 generalizes envy-cycle elimination; it is the step that the group champion graph and the rainbow cycle number feed into.
--
--   **Formalization Note** The paper's "in polynomial time, we can determine" is formalized as existence; running time is not formalized. "Champion" is read relationally as "a most envious agent". The sources, goods and agents are each required to be distinct, as "a set of" on the page says; reachability includes the case $t_i=s_i$.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 11, Lemma 10

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem lemma_10 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (s : Fin ℓ → Fin n) (g : Fin ℓ → Fin m) (t : Fin ℓ → Fin n)
    (hs_inj : Function.Injective s) (hg_inj : Function.Injective g)
    (ht_inj : Function.Injective t)
    (hs : ∀ i, IsSource v X (s i)) (hg : ∀ i, g i ∈ pool X)
    (hreach : ∀ i, Reach v X (s i) (t i))
    (hchamp : ∀ i, IsMostEnviousAgent ε v X
      (insert (g (finRotate ℓ i)) (X (s (finRotate ℓ i)))) (t i)) :
    ∃ X' : Fin n → Finset (Fin m), IsPartialAllocation X' ∧ IsAlphaEFX (1 - ε) v X' ∧
      StronglyParetoDominates ε v X' X := by sorry

end RainbowEFX.Sublinear
