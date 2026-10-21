-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_theorem_1
-- name    : RainbowEFX.Sublinear.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:41.745428+00:00
-- url     : https://prove2.me/theorems/5efea9f0-d854-461c-b512-cb0e78978187
-- title:
--   Theorem 1, p. 3 — for ε ∈ (0, 1/2] a partial (1 − ε)-EFX allocation with at most 64(n/ε)^(4/5) unallocated goods exists
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $n\ge1$ agents have additive valuations over a finite set $M$ of goods, and let $\varepsilon\in(0,1/2]$. Then there is a partial allocation $X=\langle X_1,\dots,X_n\rangle$ that is $(1-\varepsilon)$-EFX, i.e.
--   $$
--   v_i(X_i)\ \ge\ (1-\varepsilon)\,v_i(X_j\setminus\{g\})\qquad\text{for all agents } i,j \text{ and all } g\in X_j,
--   $$
--   and whose set $P$ of unallocated goods satisfies
--   $$
--   |P|\le 64\,(n/\varepsilon)^{4/5}.
--   $$
--
--   The number of goods left unallocated is sublinear in the number of agents (for fixed $\varepsilon$), improving the earlier bound $|P|\le n-1$ for exact EFX when $n$ is large.
--
--   **Formalization Note** The paper states that $X$ and $P$ can be determined in polynomial time; only their existence is formalized. $P$ is the set of goods not allocated by $X$. $n\ge1$ is added: with $n=0$ the bound is $0$ while every good is unallocated. The number $m$ of goods is arbitrary, including $0$.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 3, Theorem 1

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem theorem_1 {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∃ X : Fin n → Finset (Fin m), IsPartialAllocation X ∧ IsAlphaEFX (1 - ε) v X ∧
      ((pool X).card : ℝ) ≤ 64 * ((n : ℝ) / ε) ^ ((4 : ℝ) / 5) := by sorry

end RainbowEFX.Sublinear
