-- Prove2me | Theorems.Thm_SingleOrSample_lemma_B_4
-- name    : SingleOrSample.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:47:42.945794+00:00
-- url     : https://prove2.me/theorems/ba2a8ca2-502c-4b19-9493-6307bd5b2df1
-- title:
--   Lemma B.4 — weighted MGF bound under upper-cylinder domination
-- statement:
--   Let $G$ be a finite set and $A\subseteq G$ a random subset with $\Pr[T\subseteq A]\le p^{|T|}$ for every fixed $T\subseteq G$, for some $p\in[0,1]$. Let $(x_e)_{e\in G}$ be fixed weights in $[0,1]$, and put $X=\sum_{e\in A}x_e$ and $W=\sum_{e\in G}x_e$. For every $\lambda\ge0$,
--   $$\mathbb E[e^{\lambda X}]\le\prod_{e\in G}\bigl(1+p(e^{\lambda x_e}-1)\bigr)\le\exp\bigl(pW(e^\lambda-1)\bigr).$$
--   This converts the upper-cylinder property of a sampling round into the exponential moment used by the deficit argument.
--
--   Differences from the source:
--   - encoding: the expectation E[e^{λX}] → a sum in ℝ≥0∞ over subsets of the ground type; reason: nonnegative terms; it equals the expectation
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma B.4, eq. (12), p.32

import Mathlib

namespace SingleOrSample

/-- **Lemma B.4, weighted MGF bound under upper-cylinder domination** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma B.4, p.32). If a random
subset `A ⊆ G` has `Pr[T ⊆ A] ≤ p^|T|` for every `T ⊆ G`, and the weights lie in `[0, 1]`, then for every
`λ ≥ 0`, `E[e^{λX}] ≤ ∏_{e ∈ G}(1 + p(e^{λ x_e} − 1)) ≤ exp(pW(e^λ − 1))`, both inequalities of (12).

**Formalization Note.** The expectation is a sum in `ℝ≥0∞`, so it is meaningful with no summability
condition. -/
theorem lemma_B_4 {α : Type*} [DecidableEq α] (G : Finset α) (law : PMF (Finset α))
    (hlaw : ∀ A ∈ law.support, A ⊆ G) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcyl : ∀ T ⊆ G, law.toOuterMeasure {A | T ⊆ A} ≤ ENNReal.ofReal (p ^ T.card))
    (x : α → ℝ) (hx0 : ∀ e ∈ G, 0 ≤ x e) (hx1 : ∀ e ∈ G, x e ≤ 1) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∑' A, law A * ENNReal.ofReal (Real.exp (lam * ∑ e ∈ A, x e)) ≤
      ENNReal.ofReal (∏ e ∈ G, (1 + p * (Real.exp (lam * x e) - 1))) ∧
    ∏ e ∈ G, (1 + p * (Real.exp (lam * x e) - 1)) ≤
      Real.exp (p * (∑ e ∈ G, x e) * (Real.exp lam - 1)) := by sorry

end SingleOrSample
