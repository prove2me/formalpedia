-- Prove2me | Theorems.Thm_SecretaryWD_KnownOpt_expectedAlg_eq_good_sum
-- name    : SecretaryWD.KnownOpt.expectedAlg_eq_good_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:58:55.572749+00:00
-- url     : https://prove2.me/theorems/93707905-170d-4350-a243-cedb394aa386
-- title:
--   Eq. (4.4) — E[A] as a sum over good pairs
-- statement:
--   In the discounted secretary problem with values $v$, discounts $d$ and threshold parameter $Z$, let $G_{ij}$ be the set of orders on which the threshold algorithm $\mathcal A$ chooses element $j$ at time $i$ ($\pi(i)=j$ and every earlier product $d(k)v(\pi(k))$, $k<i$, is below $Z/2$). Then the expected value of $\mathcal A$ over a uniformly random order is
--
--   $$\mathbf E[\mathcal A]=\sum_{i=1}^n\ \sum_{j:\,d(i)v(j)\ge Z/2} d(i)\,v(j)\cdot\frac{|G_{ij}|}{|S_n|}.$$
--
--   This is the bookkeeping identity of the proof of Theorem 4.7 that rewrites the performance of the algorithm in terms of the sets $G_{ij}$, so that Claim 4.8 can be applied term by term.
--
--   **Formalization Note** $|S_n|$ is written $n!$. The identity needs no sign assumption on $d$, $v$ or $Z$ and holds for every $n$, including $n=0$ where both sides are $0$.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 8, proof of Theorem 4.7, Eq. (4.4)

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model

namespace SecretaryWD.KnownOpt

theorem expectedAlg_eq_good_sum {n : ℕ} (d v : Fin n → ℝ) (Z : ℝ) :
    expectedAlg d v Z =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => Z / 2 ≤ d i * v j),
        d i * v j * (((goodPerms d v Z i j).card : ℝ) / (n.factorial : ℝ)) := by sorry

end SecretaryWD.KnownOpt
