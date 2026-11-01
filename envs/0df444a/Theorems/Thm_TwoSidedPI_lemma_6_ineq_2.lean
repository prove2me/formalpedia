-- Prove2me | Theorems.Thm_TwoSidedPI_lemma_6_ineq_2
-- name    : TwoSidedPI.lemma_6_ineq_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:12:24.259386+00:00
-- url     : https://prove2.me/theorems/aa0c5325-c389-4855-a7b0-c79541bc15f6
-- title:
--   Proof of Lemma 6, inequality (2) (corrected: $i\notin X'$) — buyer thresholds do not decrease when $X$ grows
-- statement:
--   Let $\mathcal M_B=(B,\mathcal I_B)$ be a matroid on a finite set of buyers and $v\ge0$ a profile of buyer values. Let $X\subseteq X'\subseteq B$ and $r'\in\mathbb N$, and let buyer $i\notin X'$ be feasibly addable to $X'$ with $r'$ items: $X'\cup\{i\}\in\mathcal I_B$ and $|X'\cup\{i\}|\le r'$. Then
--   $$
--   v\big(\mathrm{OPT}_B(v\mid X,r')\big)-v\big(\mathrm{OPT}_B(v\mid X\cup\{i\},r')\big)\ \le\ v\big(\mathrm{OPT}_B(v\mid X',r')\big)-v\big(\mathrm{OPT}_B(v\mid X'\cup\{i\},r')\big)=p_i(X',r',v).
--   $$
--
--   That is, $p_i(X,r',v)\le p_i(X',r',v)$: the pointwise threshold of a buyer does not decrease as more buyers are served. The paper derives it from the submodularity of $Y\mapsto v(\mathrm{OPT}_B(v\mid Y,r'))$ in the matroid truncated to rank $r'$ (Kleinberg and Weinberg 2012, Lemma 3).
--
--   Differences from the source:
--   - correction: inequality (2) under the case "i can feasibly be added", with no condition on whether $i\in X'$ → $i\notin X'$, $X'\cup\{i\}\in\mathcal I_B$, $|X'\cup\{i\}|\le r'$; reason: with $i\in X'$ the right side is $0$ and the display fails: one buyer, $v_i=1$, $X=\emptyset$, $X'=\{i\}$, $r'=1$ gives $1\le0$ (the same correction as Lemma 6)
--   - encoding: a valuation profile $\mathbf v$ of all agents (non-negative) → the buyers' values `v : B → ℝ` with `0 ≤ v`, and `M.E = univ`; reason: only buyers' values enter $\mathrm{OPT}_B$; same instances
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, proof of Lemma 6, inequality (2), p.34

import Mathlib
import Definitions.Def_TwoSidedPI_OptB

namespace TwoSidedPI

/-- Inequality (2) in the proof of Lemma 6 (Braun, Kesselheim, arXiv:2105.15032v1, p.34),
corrected with `i ∉ X'`: for
`X ⊆ X'` and a buyer `i ∉ X'` that can feasibly be added to `X'` with `r'` items
(`X' ∪ {i} ∈ ℐ_B`, `|X' ∪ {i}| ≤ r'`),
`v(OPT_B(v|X, r')) − v(OPT_B(v|X ∪ {i}, r')) ≤ v(OPT_B(v|X', r')) − v(OPT_B(v|X' ∪ {i}, r'))`.

**Formalization Note** The hypotheses are the proof's case "i can feasibly be added" (both sides
finite). `i ∉ X'` is the correction of Lemma 6: with `i ∈ X'` the right side is `0` and the
inequality fails (one buyer `i`, `v_i = 1`, `X = ∅`, `X' = {i}`, `r' = 1`: `1 ≤ 0`). The paper derives
(2) from submodularity of `Y ↦ v(OPT_B(v|Y, r'))` (Kleinberg–Weinberg Lemma 3) in the matroid
truncated to rank `r'`. The matroid is on all of `B` and the valuation profile is nonnegative.
-/
theorem lemma_6_ineq_2 {B : Type*} [Fintype B] [DecidableEq B] (M : Matroid B)
    (hE : M.E = Set.univ) (v : B → ℝ) (hv : ∀ k, 0 ≤ v k) (i : B) (X X' : Finset B) (r' : ℕ)
    (hXX' : X ⊆ X') (hi : i ∉ X') (hind : M.Indep ↑(insert i X'))
    (hcard : (insert i X').card ≤ r') :
    optB M v X r' - optB M v (insert i X) r' ≤ optB M v X' r' - optB M v (insert i X') r' := by sorry

end TwoSidedPI
