-- Prove2me | Theorems.Thm_TwoSidedPI_lemma_6_ineq_1
-- name    : TwoSidedPI.lemma_6_ineq_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:12:34.185619+00:00
-- url     : https://prove2.me/theorems/bfb56d52-f9fb-44e0-8fd8-13f3e70e7be2
-- title:
--   Proof of Lemma 6, inequality (1) — buyer thresholds do not decrease when $r$ decreases
-- statement:
--   Let $\mathcal M_B=(B,\mathcal I_B)$ be a matroid on a finite set of buyers and $v\ge0$ a profile of buyer values. Let $X\subseteq B$, $r'\le r$, and let buyer $i$ be feasibly addable to $X$ with $r'$ items: $X\cup\{i\}\in\mathcal I_B$ and $|X\cup\{i\}|\le r'$. Then
--   $$
--   v\big(\mathrm{OPT}_B(v\mid X,r)\big)-v\big(\mathrm{OPT}_B(v\mid X\cup\{i\},r)\big)\ \le\ v\big(\mathrm{OPT}_B(v\mid X,r')\big)-v\big(\mathrm{OPT}_B(v\mid X\cup\{i\},r')\big).
--   $$
--
--   That is, $p_i(X,r,v)\le p_i(X,r',v)$: the pointwise threshold of a buyer does not decrease when fewer items remain. It is the first step of the proof of Lemma 6.
--
--   Differences from the source:
--   - reading: inequality (1) inside the proof, under the case "i can feasibly be added" → hypotheses $X\cup\{i\}\in\mathcal I_B$, $|X\cup\{i\}|\le r'$, $r'\le r$; reason: this is the case in which the display is asserted (both sides finite); it does not involve $X'$
--   - encoding: a valuation profile $\mathbf v$ of all agents (non-negative) → the buyers' values `v : B → ℝ` with `0 ≤ v`, and `M.E = univ`; reason: only buyers' values enter $\mathrm{OPT}_B$; same instances
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, proof of Lemma 6, inequality (1), p.34

import Mathlib
import Definitions.Def_TwoSidedPI_OptB

namespace TwoSidedPI

/-- Inequality (1) in the proof of Lemma 6 (Braun, Kesselheim, arXiv:2105.15032v1, p.34): for a
buyer `i` that can feasibly be added to `X` with `r'` items (`X ∪ {i} ∈ ℐ_B`,
`|X ∪ {i}| ≤ r'`) and `r' ≤ r`,
`v(OPT_B(v|X, r)) − v(OPT_B(v|X ∪ {i}, r)) ≤ v(OPT_B(v|X, r')) − v(OPT_B(v|X ∪ {i}, r'))`.

**Formalization Note** The hypotheses are the proof's case "i can feasibly be added" (both sides
finite); `i ∈ X` is allowed (both sides are then `0`). The matroid is on all of `B` and the valuation profile is nonnegative. -/
theorem lemma_6_ineq_1 {B : Type*} [Fintype B] [DecidableEq B] (M : Matroid B)
    (hE : M.E = Set.univ) (v : B → ℝ) (hv : ∀ k, 0 ≤ v k) (i : B) (X : Finset B) (r r' : ℕ)
    (hr : r' ≤ r) (hind : M.Indep ↑(insert i X)) (hcard : (insert i X).card ≤ r') :
    optB M v X r - optB M v (insert i X) r ≤ optB M v X r' - optB M v (insert i X) r' := by sorry

end TwoSidedPI
