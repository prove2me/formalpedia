-- Prove2me | Theorems.Thm_RobustDP_ChiSquareAudit_prefix_moments
-- name    : RobustDP.ChiSquareAudit.prefix_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:44:12.345945+00:00
-- url     : https://prove2.me/theorems/0da10ec4-bb55-4249-9c29-951eb4407d01
-- title:
--   Section 4.2 prefix moments (corrected: variance sign)
-- statement:
--   Let $q$ be a strictly positive probability vector on $n$ coordinates, and let $v$ be sorted in nondecreasing order, with ties allowed. Execute the single prefix pass. It returns exactly $n$ cells and takes at most $32(n+1)$ charged operations.
--
--   For every zero-based index $j$, its stored entries are
--   $$a_j=\sum_{i\le j}q_iv_i,\qquad b_j=\sum_{i>j}q_i,\qquad c_j=\sum_{i\le j}q_iv_i^2.$$
--   The lower endpoint is $v_j$; the upper endpoint is $v_{j+1}$ when that coordinate exists, and absent in the final cell. Whenever $v_i\le\alpha$ for $i\le j$ and $\alpha\le v_i$ for $i>j$, put $\mu_\alpha(i)=\max(v_i-\alpha,0)$. Then
--   $$E^q[v-\mu_\alpha]=a_j+b_j\alpha,\qquad
--   \operatorname{Var}^q[v-\mu_\alpha]=c_j+b_j\alpha^2-(a_j+b_j\alpha)^2.$$
--   For every $t\ge0$, its exact dual score is $a_j+b_j\alpha-\sqrt{t(c_j+b_j\alpha^2-(a_j+b_j\alpha)^2)}$.
--
--   These identities connect the centred moments to constant-work evaluation of every candidate. **Formalization Note** The count refers to the particular exact-real program, after sorting; no cost constant is asserted to appear in the report.
--
--   Differences from the source:
--   - correction: Var = c + b alpha^2 + (a+b alpha)^2 → Var = c + b alpha^2 - (a+b alpha)^2; reason: q=(1/3,1/3,1/3), v=(1,2,10), t=14/25, alpha=4 gives a=1, b=1/3, c=5/3, mean=7/3 and variance 14/9, whereas the printed expression gives 112/9; the next source display already uses minus
--   - encoding: one-based sorted values and O(|S|) computation of all moments → zero-based Fin n coordinates, closed endpoint identities including the final cell, and one fixed prefix pass with at most 32(n+1) charged operations; reason: the same moments are computed, the adjacent formulas agree at shared endpoints, and the final cell has b=0; the implementation constant is not attributed to the paper
-- source:
--   G. Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07, revised May 4, 2004, p. 19, Section 4.2, unnumbered displays between (53) and (54)

import Mathlib
import Definitions.Def_RobustDP_ChiSquareAudit_Program

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

/-- Section 4.2, p.19, displays after (53): the variance sign is corrected.
All sorted prefixes are computed by one execution, with a linear cost bound. -/
theorem prefix_moments (n : ℕ) (q v : Fin n → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hpos : ∀ i, 0 < q i) (hsorted : Monotone v) :
    let rows := List.ofFn (fun i : Fin n => (⟨v i, q i, i.val⟩ : Row))
    let execution := prefixPass rows 0 1 0
    execution.value.length = n ∧ execution.steps ≤ 32 * (n + 1) ∧
    ∀ j : Fin n,
      let a := ∑ i : Fin n, if i.val ≤ j.val then q i * v i else 0
      let b := ∑ i : Fin n, if j.val < i.val then q i else 0
      let c := ∑ i : Fin n, if i.val ≤ j.val then q i * v i ^ 2 else 0
      let cell := execution.value[j.val]?.getD default
      cell.low = v j ∧ cell.a = a ∧ cell.b = b ∧ cell.c = c ∧
      cell.high = (if h : j.val + 1 < n then some (v ⟨j.val + 1, h⟩) else none) ∧
      ∀ α : ℝ,
        (∀ i : Fin n, i.val ≤ j.val → v i ≤ α) →
        (∀ i : Fin n, j.val < i.val → α ≤ v i) →
        expect q (v - clippedMultiplier v α) = a + b * α ∧
        variance q (v - clippedMultiplier v α) = intervalVariance a b c α ∧
        ∀ t : ℝ, 0 ≤ t → scalarObjective q t v α = intervalObjective t a b c α := by sorry

end RobustDP.ChiSquareAudit
