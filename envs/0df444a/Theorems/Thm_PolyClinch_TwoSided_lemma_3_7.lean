-- Prove2me | Theorems.Thm_PolyClinch_TwoSided_lemma_3_7
-- name    : PolyClinch.TwoSided.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:11.907713+00:00
-- url     : https://prove2.me/theorems/9157db1f-7e0f-42ff-abe7-5183c66193f6
-- title:
--   Lemma 3.7, p. 13 — Mechanism 2 satisfies (SBB)
-- statement:
--   Let $\mathcal I$ be valid public information and $\varepsilon>0$. Every allocation $(w,p,r)$ output by Mechanism 2 (Algorithm 2 on the extended market, followed by the transformation $r_j\mapsto r_j-p_{n+j}$ and the restriction to real buyers) satisfies strong budget balance:
--   $$
--   \sum_{i\in N}p_i=\sum_{j\in M}r_j .
--   $$
--   In each iteration the payments of all buyers, virtual ones included, are passed to the sellers (line 10), and the transformation subtracts the virtual buyers' payments from both sides.
--
--   **Formalization Note** "Output of Mechanism 2" is the relation `Mech2Outcome`: the transformation of any terminal state of any run of Algorithm 2.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, p. 13, Lemma 3.7

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Clinching

namespace PolyClinch.TwoSided

/-- Lemma 3.7 (Hirai–Sato p. 13). Mechanism 2 satisfies (SBB): every output `A` of Mechanism 2 on
a valid input has `∑_i p_i = ∑_j r_j`. -/
theorem lemma_3_7 {n m : ℕ} (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε)
    (I : PublicInfo E) (hI : Valid E ε I) (A : Allocation E) (hA : Mech2Outcome E I ε A) :
    ∑ i, A.p i = ∑ j, A.r j := by sorry

end PolyClinch.TwoSided
