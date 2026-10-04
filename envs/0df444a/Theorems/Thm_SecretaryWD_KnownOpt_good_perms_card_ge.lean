-- Prove2me | Theorems.Thm_SecretaryWD_KnownOpt_good_perms_card_ge
-- name    : SecretaryWD.KnownOpt.good_perms_card_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:58:55.960754+00:00
-- url     : https://prove2.me/theorems/e0478c29-368c-4d03-9e51-c051a1dcd720
-- title:
--   Claim 4.8 — |G_ij| ≥ |S_n ∖ S_acc|/n ≥ |S_n|/2n
-- statement:
--   Consider the discounted secretary problem with $n\ge1$ elements, values $v\ge0$, discounts $d\ge0$ and a real threshold parameter $Z$. Let $S_{acc}$ be the accepting permutations ($\max_i d(i)v(\pi(i))\ge Z/2$), and for a time $i$ and an element $j$ let $G_{ij}$ be the set of orders with $\pi(i)=j$ and $d(k)v(\pi(k))<Z/2$ for all $k<i$, on which the threshold algorithm chooses $j$ at time $i$. For each $i,j$ with $d(i)v(j)\ge Z/2$:
--
--   1. $n\,|G_{ij}|\ \ge\ |S_n\setminus S_{acc}|$, unconditionally;
--   2. if at most half of the permutations are accepting, $2|S_{acc}|\le|S_n|=n!$, then $2n\,|G_{ij}|\ge n!$.
--
--   Together these are the paper's $|G_{ij}|\ge|S_n\setminus S_{acc}|/n\ge|S_n|/2n$. The second inequality is used only in the second case of the proof of Theorem 4.7, where the algorithm picks an element with probability less than $1/2$; the paper's sentence "at most half the permutations are in $S_{acc}$" is that case hypothesis, and it is a hypothesis of part 2 here.
--
--   The claim says that every good pair is realised by the algorithm on a $1/(2n)$ fraction of the orders, which with Eq. (4.4) and Eq. (4.3) gives $\mathbf E[\mathcal A]\ge Z/4$.
--
--   **Formalization Note** Both inequalities are stated in cleared-denominator form on natural numbers; $|S_n|$ is written $n!$.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 8, Claim 4.8

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model

namespace SecretaryWD.KnownOpt

theorem good_perms_card_ge {n : ℕ} [NeZero n] (d v : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hv : ∀ e, 0 ≤ v e) (Z : ℝ) (i j : Fin n)
    (hij : Z / 2 ≤ d i * v j) :
    (Finset.univ \ acceptingPerms d v Z).card ≤ n * (goodPerms d v Z i j).card ∧
      (2 * (acceptingPerms d v Z).card ≤ n.factorial →
        n.factorial ≤ 2 * n * (goodPerms d v Z i j).card) := by sorry

end SecretaryWD.KnownOpt
