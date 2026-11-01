-- Prove2me | Theorems.Thm_TwoSidedPI_lemma_8
-- name    : TwoSidedPI.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:12:22.952451+00:00
-- url     : https://prove2.me/theorems/d835cc87-4c2b-41a0-ab1e-4b6bf9bc994b
-- title:
--   Lemma 8 — adapted Kleinberg–Weinberg Proposition 2
-- statement:
--   Let $\mathcal M_B=(B,\mathcal I_B)$ be a matroid on a finite set of buyers, $r\in\mathbb N$, and let $\mathcal I_r=\{X\in\mathcal I_B:|X|\le r\}$ be the independent sets of $\mathcal M_B$ truncated to rank $r$. Fix a nonnegative profile $\tilde v$ of buyer values and $A_B\in\mathcal I_r$. For every set $V$ disjoint from $A_B$ with $V\in\mathcal I_r$ and $A_B\cup V\in\mathcal I_r$,
--   $$
--   \sum_{i\in V}p_i(A_B,r,\tilde v)\ \le\ \tilde v\big(\mathrm{OPT}_B(\tilde v\mid A_B,r)\big).
--   $$
--
--   Each $p_i(A_B,r,\tilde v)$ with $i\in V$ is finite here. The lemma bounds the total threshold of any set of buyers that can extend $A_B$ by the remaining buyers-only optimum; the paper applies it with $V=\mathrm{OPT}_B(\mathbf v'\mid A_B(\mathbf v),r(\mathbf v))$ to bound the buyers' surplus.
--
--   Differences from the source:
--   - encoding: $A_B\in\mathcal I_r$, $V\in\mathcal I_r$ and $A_B\cup V\in\mathcal I_r$, with $\mathcal I_r$ the truncated matroid → only $M.\mathrm{Indep}(A_B\cup V)$ and $|A_B\cup V|\le r$, with $\mathcal I_r$ written out; reason: $A_B\in\mathcal I_r$ and $V\in\mathcal I_r$ follow from $A_B\cup V\in\mathcal I_r$; same instances
--   - encoding: a real sum of finite thresholds → the sum taken in `WithTop ℝ`; reason: every summand is finite under the hypotheses; same value
--   - encoding: a valuation profile $\mathbf v$ of all agents (non-negative) → the buyers' values `v : B → ℝ` with `0 ≤ v`, and `M.E = univ`; reason: only buyers' values enter $\mathrm{OPT}_B$; same instances
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, Lemma 8, p.36

import Mathlib
import Definitions.Def_TwoSidedPI_OptB

namespace TwoSidedPI

/-- Lemma 8 (Braun, Kesselheim, arXiv:2105.15032v1, p.36; adapted Kleinberg–Weinberg 2012,
Proposition 2): fix a valuation profile `ṽ` and `r`, and let `A_B ∈ ℐ_r`; for every set `V`
disjoint from `A_B` with `V ∈ ℐ_r` and `A_B ∪ V ∈ ℐ_r`,
`∑_{i ∈ V} p_i(A_B, r, ṽ) ≤ ṽ(OPT_B(ṽ|A_B, r))`, where `X ∈ ℐ_r ⇔ X ∈ ℐ_B ∧ |X| ≤ r` (the
matroid `M_B` truncated to rank `r`).

**Formalization Note** `ℐ_r` is written out as `M.Indep ↑X ∧ X.card ≤ r`. The hypotheses
`A_B ∈ ℐ_r` and `V ∈ ℐ_r` follow from `A_B ∪ V ∈ ℐ_r` and are not repeated. Every `p_i` with
`i ∈ V` is finite here; the sum is taken in `WithTop ℝ`. The matroid is on all of `B` and the
valuation profile is nonnegative. -/
theorem lemma_8 {B : Type*} [Fintype B] [DecidableEq B] (M : Matroid B) (hE : M.E = Set.univ)
    (v : B → ℝ) (hv : ∀ k, 0 ≤ v k) (r : ℕ) (AB V : Finset B) (hdisj : Disjoint AB V)
    (hind : M.Indep ↑(AB ∪ V)) (hcard : (AB ∪ V).card ≤ r) :
    ∑ i ∈ V, thrPt M v AB r i ≤ (optB M v AB r : WithTop ℝ) := by sorry

end TwoSidedPI
