-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_lemma_8
-- name    : RainbowEFX.Sublinear.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:12.840245+00:00
-- url     : https://prove2.me/theorems/d80f3a81-840a-4583-b2be-2cc115c97a82
-- title:
--   Lemma 8 (U1 [19]), p. 11 — giving an unallocated good g to a source s keeps (1 − ε)-EFX if nobody strongly envies X_s ∪ g
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $0<\varepsilon<1$ and let $X$ be a $(1-\varepsilon)$-EFX allocation. Suppose $s$ is a source of the envy graph $E_X$ (nobody envies $s$), $g$ is an unallocated good, and no agent strongly envies $X_s\cup\{g\}$. Let
--   $$
--   X'=\langle X_1,X_2,\dots,X_s\cup\{g\},\dots,X_n\rangle .
--   $$
--   Then $X'$ is a $(1-\varepsilon)$-EFX allocation and $v_i(X'_i)\ge v_i(X_i)$ for all $i\in[n]$.
--
--   Rule U1 reduces the number of unallocated goods by one without making anyone worse off.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 11, Lemma 8

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem lemma_8 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (s : Fin n) (hs : IsSource v X s) (g : Fin m) (hg : g ∈ pool X)
    (hno : ∀ i, ¬ StronglyEnvies ε v X i (insert g (X s))) :
    IsPartialAllocation (Function.update X s (insert g (X s))) ∧
      IsAlphaEFX (1 - ε) v (Function.update X s (insert g (X s))) ∧
      ∀ i, v i (X i) ≤ v i (Function.update X s (insert g (X s)) i) := by sorry

end RainbowEFX.Sublinear
