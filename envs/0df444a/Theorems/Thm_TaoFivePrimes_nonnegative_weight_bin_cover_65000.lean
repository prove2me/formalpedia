-- Prove2me | Theorems.Thm_TaoFivePrimes_nonnegative_weight_bin_cover_65000
-- name    : TaoFivePrimes.nonnegative_weight_bin_cover_65000
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:06:43.008927+00:00
-- url     : https://prove2.me/theorems/15a489ba-27d4-4610-8802-948cd706e37f
-- title:
--   A finite nonnegative-weight cover by 180 height bins
-- statement:
--   Let $S$ be a finite set, let $\gamma:S\to\mathbb R$ satisfy $65000<\gamma(x)\le297200$, and let $w(x)\ge0$ on $S$. Put $L_i=65000+1290i$ and $U_i=L_i+1290$ for $0\le i<180$. Then
--
--   $$
--   \sum_{x\in S}w(x)\le\sum_{i=0}^{179}\ \sum_{\substack{x\in S\\L_i<\gamma(x)\le U_i}}w(x).
--   $$
--
--   The strict lower and closed upper endpoints cover the full interval without omitting boundary values.
-- source:
--   Elementary finite-sum cover used for the Tao five-primes Chebyshev-error reduction.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

theorem TaoFivePrimes.nonnegative_weight_bin_cover_65000 {α : Type*} [DecidableEq α] (S : Finset α) (γ w : α → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x)
    (hlo : ∀ x ∈ S, 65000 < γ x)
    (hhi : ∀ x ∈ S, γ x ≤ 297200) :
    (∑ x ∈ S, w x) ≤
      ∑ i ∈ Finset.range 180,
        ∑ x ∈ S.filter (fun x => 65000+1290*(i:ℝ) < γ x ∧
          γ x ≤ 65000+1290*((i:ℝ)+1)), w x := by sorry
