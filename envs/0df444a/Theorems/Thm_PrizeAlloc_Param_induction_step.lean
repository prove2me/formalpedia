-- Prove2me | Theorems.Thm_PrizeAlloc_Param_induction_step
-- name    : PrizeAlloc.Param.induction_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:13.782889+00:00
-- url     : https://prove2.me/theorems/671cfcc3-d102-466a-b009-a859b23ea6cd
-- title:
--   Proof of Theorem 3, p. 33 — induction step: a parametric representation on at most n competitors extends to n + 1 competitors
-- statement:
--   Let $\varphi$ be a prize allocation rule satisfying anonymity, order preservation, winner strict endowment monotonicity, top consistency and endowment continuity. Let $n\ge 1$ and suppose there are functions $f_1,\dots,f_n:\mathbb R_+\to\mathbb R_+$, continuous and non-decreasing, with $f_1(x)=x$ for each $x$ and $f_{k+1}(x)\le f_k(x)$ for $1\le k<n$, such that for each competition $(N,\mathcal R,E)$ with $|N|\le n$ and each $i\in N$,
--
--   $$\varphi_i(N,\mathcal R,E)=f_{\mathcal R(i)}(x),\qquad \sum_{k=1}^{|N|}f_k(x)=E .$$
--
--   Then there is a continuous non-decreasing $f_{n+1}:\mathbb R_+\to\mathbb R_+$ with $f_{n+1}(x)\le f_n(x)$ for each $x\ge 0$ such that the same formula, with representation $f_1,\dots,f_{n+1}$, holds for every competition with exactly $n+1$ competitors.
--
--   Together with the trivial base case $|N|=1$ (where $\varphi_i=E=f_1(x)$), this step yields the "only if" direction of Theorem 3 by induction on the number of competitors.
--
--   **Formalization Note** The page writes "Let $n\in\mathbb N$"; the base case is $|N|=1$, so $n\ge 1$. The page's "$f_{k+1}(x)\le f_k(x)$ for each $k$" refers to the functions $f_1,\dots,f_n$ already given, so it is assumed for $1\le k<n$. The new function is written $g$ and the extended representation is $f$ with its $(n+1)$-st entry replaced by $g$. The conclusion is asserted for every ranking of length $n+1$ (when $U$ has fewer than $n+1$ elements it is vacuous apart from the properties of $g$). Endowment continuity is a hypothesis, as in the proof, where it comes from Lemma 1.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, pp. 32–33, proof of Theorem 3, induction hypothesis (p. 32) and induction step (p. 33)

import Mathlib
import Definitions.Def_PrizeAlloc_Param_Setting
import Definitions.Def_PrizeAlloc_Param_ParametricRule

namespace PrizeAlloc.Param

/-- Proof of Theorem 3, induction step (pp. 32–33): if `φ` is parametric with representation
`f 1, …, f n` on all competitions with at most `n` competitors, then there is a continuous,
non-decreasing `f (n+1) : ℝ₊ → ℝ₊` with `f (n+1) ≤ f n` such that `φ` is parametric with
representation `f 1, …, f (n+1)` on all competitions with `n + 1` competitors. -/
theorem induction_step {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ)
    (hA : PrizeAlloc.Interval.Anonymous φ) (hOP : PrizeAlloc.Interval.OrderPreserving φ) (hWSM : PrizeAlloc.Interval.WinnerStrictMonotone φ)
    (hTC : TopConsistent φ) (hEC : PrizeAlloc.Interval.EndowmentContinuous φ)
    (n : ℕ) (hn : 1 ≤ n) (f : ℕ → ℝ → ℝ)
    (hf1 : ∀ x, 0 ≤ x → f 1 x = x)
    (hfk : ∀ k, 1 ≤ k → k ≤ n →
      ContinuousOn (f k) (Set.Ici 0) ∧ MonotoneOn (f k) (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ f k x)
    (hfdec : ∀ k, 1 ≤ k → k < n → ∀ x, 0 ≤ x → f (k + 1) x ≤ f k x)
    (hrule : ∀ l E, PrizeAlloc.Interval.IsRanking l → l.length ≤ n → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.Icc 1 l.length, f k x) = E ∧
        ∀ i ∈ l, φ l E i = f (PrizeAlloc.Interval.pos l i) x) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Set.Ici 0) ∧ MonotoneOn g (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ g x ∧ g x ≤ f n x) ∧
      ∀ l E, PrizeAlloc.Interval.IsRanking l → l.length = n + 1 → 0 ≤ E →
        ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.Icc 1 l.length, Function.update f (n + 1) g k x) = E ∧
          ∀ i ∈ l, φ l E i = Function.update f (n + 1) g (PrizeAlloc.Interval.pos l i) x := by sorry

end PrizeAlloc.Param
