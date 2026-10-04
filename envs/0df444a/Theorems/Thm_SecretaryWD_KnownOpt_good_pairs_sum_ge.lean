-- Prove2me | Theorems.Thm_SecretaryWD_KnownOpt_good_pairs_sum_ge
-- name    : SecretaryWD.KnownOpt.good_pairs_sum_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:58:33.582586+00:00
-- url     : https://prove2.me/theorems/ef25ee6a-87d9-4feb-9efd-599593c56985
-- title:
--   Eq. (4.3) — the good pairs (i, j) carry at least Z/2
-- statement:
--   Consider the discounted secretary problem with $n\ge1$ elements, values $v\ge0$ and discounts $d\ge0$, and let $Z\le\mathbf E[\mathrm{OPT}]$. Call a pair of a time $i$ and an element $j$ good if $d(i)v(j)\ge Z/2$. Then
--
--   $$\sum_{i=1}^n\ \sum_{j:\,d(i)v(j)\ge Z/2}\frac1n\cdot d(i)\,v(j)\;\ge\;\frac Z2.$$
--
--   In the paper this follows by writing the contribution $L$ of the accepting permutations as a sum over good pairs, Eq. (4.2), and combining it with Eq. (4.1). It turns the bound on $L$ into a bound that no longer refers to the random order and is the quantity the final estimate of Theorem 4.7 compares against.
--
--   **Formalization Note** The inner sum ranges over the elements $j$ (`Fin n`) with $Z/2\le d(i)v(j)$, a non-strict inequality as in the paper.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 8, proof of Theorem 4.7, Eq. (4.3)

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model

namespace SecretaryWD.KnownOpt

theorem good_pairs_sum_ge {n : ℕ} [NeZero n] (d v : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hv : ∀ e, 0 ≤ v e) (Z : ℝ) (hZ : Z ≤ expectedOPT d v) :
    Z / 2 ≤ ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => Z / 2 ≤ d i * v j),
      (1 / (n : ℝ)) * (d i * v j) := by sorry

end SecretaryWD.KnownOpt
