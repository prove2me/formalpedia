-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_lemma_16
-- name    : RainbowEFX.Sublinear.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:17.666935+00:00
-- url     : https://prove2.me/theorems/0b28c85c-76c9-4202-8e1a-46648d9854ab
-- title:
--   Lemma 16, p. 14 — under (*), if |L_X| > d⁴ + d then there is a (1 − ε)-EFX allocation X′ >_PD X
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $n\ge1$, $0<\varepsilon\le1/2$, $d\ge1$, and let $X$ be a $(1-\varepsilon)$-EFX allocation satisfying assumption (\*) of §4. Let $L_X$ be the set of unallocated goods valuable to at most $d$ agents. If
--   $$
--   |L_X|>d^4+d,
--   $$
--   then there is a $(1-\varepsilon)$-EFX allocation $X'$ with $X'>_{PD}X$.
--
--   This is Lemma 15 with the bound $R(d)\le d^4+d$ of Theorem 3 substituted.
--
--   **Formalization Note** The paper's "in polynomial time, we can determine" is formalized as existence; running time is not formalized. Assumption (\*) is not in the lemma's sentence but is the standing assumption of §4 ("for most of this section, we proceed under the assumption (\*)"); without it rule U1 may apply and no strongly Pareto-dominating allocation need exist. $n\ge1$ is added: with no agents nothing can be dominated, while (\*) holds trivially.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 14, Lemma 16 (Lemma 15, p. 13, with R(d) ≤ d⁴ + d)

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem lemma_16 {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (d : ℕ) (hd : 1 ≤ d) (hstar : Star ε v X) (hL : d ^ 4 + d < (LX ε v X d).card) :
    ∃ X' : Fin n → Finset (Fin m), IsPartialAllocation X' ∧ IsAlphaEFX (1 - ε) v X' ∧
      StronglyParetoDominates ε v X' X := by sorry

end RainbowEFX.Sublinear
