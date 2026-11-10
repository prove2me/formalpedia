-- Prove2me | Theorems.Thm_PairwiseRealize_eq_3_1_rectangle_switch
-- name    : PairwiseRealize.eq_3_1_rectangle_switch
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:55:44.501642+00:00
-- url     : https://prove2.me/theorems/5e868173-55d5-449d-869e-35ba49589976
-- title:
--   (3.1), p.6 — the rectangle switch preserves total and singletons and changes only the block $A\times B$
-- statement:
--   Let $A,B$ be disjoint coordinate groups and let $x_1=(u,w)$, $x_2=(v,z)$ be rows that agree outside $A\cup B$. Let $y_1=(u,z)$ take $x_1$ on $A$ and outside and $x_2$ on $B$, and let $y_2=(v,w)$ be the reverse. The change $w_{x_1}+w_{x_2}-w_{y_1}-w_{y_2}$ vanishes on the total and on every singleton. On a pair $\{i,j\}$ with one coordinate in $A$ and the other in $B$ it equals
--
--   $$(x_{1,i}-x_{2,i})(x_{1,j}-x_{2,j})=(u_i-v_i)(w_j-z_j),$$
--
--   and on every other pair it vanishes.
--
--   This locality is what allows separate blocks of pairwise statistics to be repaired independently.
--
--   Differences from the source:
--   - encoding: pairs indexed by i ∈ A, j ∈ B; "a rank-one matrix" → unordered pairs written i < j, both orders of A and B covered; the rank-one claim is the displayed product form; reason: coordinates are unordered pairs in this mission; a product of a vector on A and a vector on B is the rank-one statement
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §3.1, (3.1), p.6 (PDF p.7)

import Mathlib
import Definitions.Def_PairwiseRealize_Model

namespace PairwiseRealize

/-- **The rectangle switch (3.1), §3.1 p.6 (PDF p.7).** K. Shi, H. Sun, *Robust Exact Realization of
Pairwise Boolean Statistics*, STOC 2027 submission (manuscript sha256 62090516…): "For disjoint
coordinate groups A and B, consider two pairs of rows that agree outside A ∪ B. The rectangle switch
is {(u, w), (v, z)} ←→ {(u, z), (v, w)}. (3.1) It preserves the number of rows and all singleton
counts. For i ∈ A and j ∈ B, the change in the pair count is uᵢwⱼ + vᵢzⱼ − uᵢzⱼ − vᵢwⱼ =
(uᵢ − vᵢ)(wⱼ − zⱼ). Pairs within A or within B are unchanged […] Pairs involving a coordinate outside
A ∪ B are unchanged".

Rows `x₁ = (u, w)` and `x₂ = (v, z)` agree outside `A ∪ B`; `y₁ = (u, z)` takes `x₁` on `A` and
outside and `x₂` on `B`, and `y₂ = (v, w)` the reverse. The change
`w_{x₁} + w_{x₂} − w_{y₁} − w_{y₂}` vanishes on the total and on every singleton, equals
`(x₁ᵢ − x₂ᵢ)(x₁ⱼ − x₂ⱼ) = (uᵢ − vᵢ)(wⱼ − zⱼ)` on a pair `{i, j}` with one coordinate in `A` and the
other in `B`, and vanishes on every other pair.

**Formalization Note** Pairs are unordered and written `{i, j}` with `i < j`; "one coordinate in
`A`, the other in `B`" covers both orders. -/
theorem eq_3_1_rectangle_switch (n : ℕ) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (x₁ x₂ : Row n) (hout : ∀ i, i ∉ A ∪ B → x₁ i = x₂ i) :
    let y₁ : Row n := fun i => if i ∈ B then x₂ i else x₁ i
    let y₂ : Row n := fun i => if i ∈ B then x₁ i else x₂ i
    let Δ : Feat n → ℤ := fun f => wvec n x₁ f + wvec n x₂ f - wvec n y₁ f - wvec n y₂ f
    Δ Feat.total = 0 ∧ (∀ i, Δ (Feat.single i) = 0) ∧
      ∀ i j (h : i < j), Δ (Feat.pair i j h) =
        if (i ∈ A ∧ j ∈ B) ∨ (i ∈ B ∧ j ∈ A) then
          (bv (x₁ i) - bv (x₂ i)) * (bv (x₁ j) - bv (x₂ j))
        else 0 := by sorry

end PairwiseRealize
