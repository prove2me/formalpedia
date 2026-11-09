-- Prove2me | Theorems.Thm_WeightedEdgeColor_proposition_A_5
-- name    : WeightedEdgeColor.proposition_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:45:28.132217+00:00
-- url     : https://prove2.me/theorems/b2a068c5-316b-43c5-b5b5-9e1c84fd4766
-- title:
--   Proposition A.5 — disjoint listed sets covering $A$ (Delcourt–Postle)
-- statement:
--   Let $A$ and $B$ be disjoint sets of elements. Consider a finite list of sets, each contained in $A\cup B$ and containing exactly one element of $A$ and at most two elements of $B$; the same set may occur several times. Write $d(x)$ for the number of listed sets containing $x$, and $\Delta_2$ for the largest number of listed sets containing any given pair of distinct elements; all counts include repetitions.
--
--   Fix $\zeta>0$. There are a constant $a>0$ and a threshold $D_0$ such that for every $D\ge D_0$ the conditions
--   $$
--   d(x)\ge(1+D^{-a})D\ (x\in A),\qquad d(y)\le D\ (y\in B),\qquad \Delta_2\le D^{1-\zeta}
--   $$
--   guarantee a collection of pairwise disjoint listed sets covering every element of $A$.
--
--   In the rounding of Theorem 3.1, elements of $A$ are edges to be colored, elements of $B$ are available slots at their endpoints, and a listed set is one option for an edge; the collection chooses every edge once and uses every slot at most once. This is Theorem 2.6 of Delcourt and Postle for sets of size at most three, imported by the paper.
--
--   **Formalization Note** The list is a family of finite sets indexed by a finite type, and a collection is a set of indices whose sets are pairwise disjoint. $\Delta_2\le D^{1-\zeta}$ is stated for every pair of distinct elements.
--
--   Differences from the source:
--   - reading: "for all sufficiently large $D$" (type of $D$ unstated) → every real $D\ge D_0$; reason: the stronger reading; integer $D$ is a special case
--   - reading: sets containing one element of $A$ and at most two of $B$ → sets contained in $A\cup B$ with these counts; reason: the listed sets are sets of the elements of $A$ and $B$
--   - encoding: finite list of sets, $\Delta_2$ a maximum → a family indexed by a finite type, the pair count bounded for every pair of distinct elements; reason: the same counts with repetitions; a bound on every pair is a bound on the maximum
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Proposition A.5, p.26 (citing Delcourt–Postle [DP24, Theorem 2.6])

import Mathlib

set_option autoImplicit false

namespace WeightedEdgeColor

/-- Proposition A.5 (Choosing disjoint sets, Delcourt–Postle [DP24, Theorem 2.6]).

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Proposition A.5, p.26. Imported result ([DP24, Theorem 2.6] for sets of size at most three).

**Formalization Note.** The finite list of sets is a family `S : ι → Finset α` over a finite
index type `ι`, so a set may occur several times and all counts include repetitions:
`d(x) = #{i | x ∈ S i}` and `Δ₂ = max_{x ≠ y} #{i | x ∈ S i ∧ y ∈ S i}` (the latter as a bound
for every pair of distinct elements). Each listed set lies in `A ∪ B`. `D` is a real number
(the stronger reading of "sufficiently large D"); `a` and the threshold `D₀` depend only on `ζ`.
A collection of listed sets is a set `M` of indices, pairwise disjoint for distinct indices. -/
theorem proposition_A_5 (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ a : ℝ, 0 < a ∧ ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      ∀ (α ι : Type) [DecidableEq α] [Fintype ι] (A B : Finset α) (S : ι → Finset α),
      Disjoint A B →
      (∀ i, S i ⊆ A ∪ B ∧ (S i ∩ A).card = 1 ∧ (S i ∩ B).card ≤ 2) →
      (∀ x ∈ A, (1 + D ^ (-a)) * D ≤ ((Finset.univ.filter (fun i => x ∈ S i)).card : ℝ)) →
      (∀ y ∈ B, ((Finset.univ.filter (fun i => y ∈ S i)).card : ℝ) ≤ D) →
      (∀ x y : α, x ≠ y →
        ((Finset.univ.filter (fun i => x ∈ S i ∧ y ∈ S i)).card : ℝ) ≤ D ^ (1 - ζ)) →
      ∃ M : Finset ι, (∀ i ∈ M, ∀ j ∈ M, i ≠ j → Disjoint (S i) (S j)) ∧
        ∀ x ∈ A, ∃ i ∈ M, x ∈ S i := by sorry

end WeightedEdgeColor
