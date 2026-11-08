-- Prove2me | Theorems.Thm_TwoSidedPI_lemma_5
-- name    : TwoSidedPI.lemma_5
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:12:27.795729+00:00
-- url     : https://prove2.me/theorems/92174442-cecc-471b-87b0-c8cc37abc168
-- title:
--   Lemma 5 (corrected: $i\notin A_B$) — a seller keeping costs at most a sale
-- statement:
--   Let $\mathcal M_B=(B,\mathcal I_B)$ be a matroid on a finite set of buyers and $v\ge0$ a profile of buyer values. Fix a buyer $i\notin A_B$ and $r\in\mathbb N$ with $A_B\cup\{i\}\in\mathcal I_B$ and $|A_B\cup\{i\}|\le r$. Then
--   $$
--   v\big(\mathrm{OPT}_B(v\mid A_B,r)\big)-v\big(\mathrm{OPT}_B(v\mid A_B\cup\{i\},r)\big)\ \ge\ v\big(\mathrm{OPT}_B(v\mid A_B,r)\big)-v\big(\mathrm{OPT}_B(v\mid A_B,r-1)\big).
--   $$
--
--   In the analysis of Mechanism 1 this bounds the loss in the buyers-only optimum when a seller keeps her item ($r$ drops by one) by the loss when the item is sold to buyer $i$.
--
--   Differences from the source:
--   - correction: no condition on whether $i\in A_B$ → $i\notin A_B$; reason: the printed lemma fails for $i\in A_B$: free matroid on $\{i,k\}$, $v=(0,1)$, $A_B=\{i\}$, $r=2$ gives $0\ge1$; the mechanism only prices buyers outside $A_B$
--   - encoding: a valuation profile $\mathbf v$ of all agents (non-negative) → the buyers' values `v : B → ℝ` with `0 ≤ v`, and `M.E = univ`; reason: only buyers' values enter $\mathrm{OPT}_B$; same instances
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, Lemma 5, p.34

import Mathlib
import Definitions.Def_TwoSidedPI_OptB

namespace TwoSidedPI

/-- Lemma 5 (Braun, Kesselheim, arXiv:2105.15032v1, p.34), corrected with `i ∉ A_B`: for a buyer
`i ∉ A_B` with `A_B ∪ {i} ∈ ℐ_B` and `|A_B ∪ {i}| ≤ r`,
`v(OPT_B(v|A_B, r)) − v(OPT_B(v|A_B ∪ {i}, r)) ≥ v(OPT_B(v|A_B, r)) − v(OPT_B(v|A_B, r − 1))`.

**Formalization Note** The printed lemma omits `i ∉ A_B` and is false without it (free matroid on
`{i, k}`, `v = (0, 1)`, `A_B = {i}`, `r = 2`: `0 ≥ 1`). `r − 1` is natural-number subtraction;
the hypotheses give `r ≥ 1`. The matroid is on all of `B` (`M.E = univ`) and the valuation profile
is nonnegative. -/
theorem lemma_5 {B : Type*} [Fintype B] [DecidableEq B] (M : Matroid B) (hE : M.E = Set.univ)
    (v : B → ℝ) (hv : ∀ k, 0 ≤ v k) (i : B) (AB : Finset B) (r : ℕ)
    (hi : i ∉ AB) (hind : M.Indep ↑(insert i AB)) (hcard : (insert i AB).card ≤ r) :
    optB M v AB r - optB M v (insert i AB) r ≥ optB M v AB r - optB M v AB (r - 1) := by sorry

end TwoSidedPI
