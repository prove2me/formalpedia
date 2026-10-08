-- Prove2me | Theorems.Thm_RetailVariety_Structure_theorem_1
-- name    : RetailVariety.Structure.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:15.149732+00:00
-- url     : https://prove2.me/theorems/27505357-9422-4746-a37b-6d93c8252757
-- title:
--   Theorem 1: some most-popular set $A_i=\{1,\dots,i\}$ maximizes store profit, under both demand models
-- statement:
--   Let the category have $n\ge1$ variants with preferences sorted in decreasing order, $v_1\ge v_2\ge\cdots\ge v_n>0$, and no-purchase preference $v_0>0$. Let the price $p$ and unit cost $c$ satisfy $0<c<p$, and let $\lambda>0$, $\sigma>0$, $0\le\beta<1$. Write $A_i=\{1,\dots,i\}$ for the set of the $i$ most popular variants ($A_0=\emptyset$).
--
--   1. **Independent population model.** There is $i$ with $0\le i\le n$ such that
--   $$\pi_I(S,v)\le\pi_I(A_i,v)\qquad\text{for every }S\subseteq N .$$
--   2. **Trend-following population model.** There is $i$ with $1\le i\le n$ such that
--   $$\pi_T(S,v)\le\pi_T(A_i,v)\qquad\text{for every }S\subseteq N .$$
--
--   Here $\pi_I$ and $\pi_T$ are the store profits (7) and (8). Thus the retailer's choice among $2^n$ assortments reduces to a choice among the $n+1$ (respectively $n$) nested most-popular sets, even though the most profitable assortment of a *given* size need not consist of the most popular variants.
--
--   **Formalization Note** The paper states $S^*\in\{A_1,\dots,A_n\}$ for both models. In the independent model $\pi_I(A_1,v)=(p-c)\lambda q_1-p\sigma\lambda^\beta\varphi(z)q_1^\beta$ is negative for small $\lambda$, and then the empty assortment (profit $0$) is the unique optimum over all $S\subseteq N$; the formal statement therefore allows $i=0$ there. In the trend-following model $\pi_T\ge0=\pi_T(\emptyset,v)$, and the printed range $1\le i\le n$ is kept. The sorting $v_1\ge\cdots\ge v_n$ (the paper's "without loss of generality", §3.1) is the hypothesis `Antitone v`.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1503, Theorem 1

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model

namespace RetailVariety.Structure

/-- Theorem 1, p. 1503: with the variants sorted by decreasing preference, some most-popular set
`A_i = {1, …, i}` maximizes store profit over all assortments `S ⊆ N`, for each of the two
demand models. Independent model: `0 ≤ i ≤ n` (`A_0 = ∅` is needed when every nonempty
assortment loses money). Trend-following model: `1 ≤ i ≤ n`, as printed. -/
theorem theorem_1 (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (hanti : Antitone v) (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p)
    (hlam : 0 < lam) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∃ i : ℕ, i ≤ n ∧ ∀ S : Finset (Fin n),
        profitI p c lam σ β v v0 S ≤ profitI p c lam σ β v v0 (popularSet n i)) ∧
      (∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ ∀ S : Finset (Fin n),
        profitT p c lam v v0 S ≤ profitT p c lam v v0 (popularSet n i)) := by sorry

end RetailVariety.Structure
