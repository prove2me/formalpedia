-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_lemma_6
-- name    : RainbowEFX.Sublinear.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:01.517817+00:00
-- url     : https://prove2.me/theorems/62d5c29b-43e7-4fe1-acd0-9d6b10a24d3d
-- title:
--   Lemma 6 ([31]), p. 10 — envy-cycle elimination keeps (1 − ε)-EFX, makes E_X acyclic, and no agent is worse off
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $0<\varepsilon<1$ and let $X$ be a $(1-\varepsilon)$-EFX allocation. If the envy graph $E_X$ (edge $i\to j$ iff $v_i(X_i)<v_i(X_j)$) has a cycle, then there is a $(1-\varepsilon)$-EFX allocation $X'$ such that
--   $$
--   v_i(X'_i)\ge v_i(X_i)\quad\text{for all } i\in[n],
--   $$
--   $E_{X'}$ is acyclic, and $X'$ leaves exactly the same goods unallocated as $X$.
--
--   Envy-cycle elimination is the first step of every iteration of the paper's algorithm.
--
--   **Formalization Note** The paper's "in polynomial time, we can determine" is formalized as existence; running time is not formalized. The equality of the pools is not in the lemma's sentence; it is taken from footnote 7 on p. 10 (bundles are passed along the cycle, so the set of allocated goods is unchanged), and the paper's termination argument uses it.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 10, Lemma 6 and footnote 7

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem lemma_6 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (hcyc : ∃ i, Relation.TransGen (Envies v X) i i) :
    ∃ X' : Fin n → Finset (Fin m), IsPartialAllocation X' ∧ IsAlphaEFX (1 - ε) v X' ∧
      (∀ i, v i (X i) ≤ v i (X' i)) ∧ EnvyAcyclic v X' ∧ pool X' = pool X := by sorry

end RainbowEFX.Sublinear
