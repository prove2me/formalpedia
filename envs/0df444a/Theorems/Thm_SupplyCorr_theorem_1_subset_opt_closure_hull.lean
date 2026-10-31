-- Prove2me | Theorems.Thm_SupplyCorr_theorem_1_subset_opt_closure_hull
-- name    : SupplyCorr.theorem_1_subset_opt_closure_hull
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:45.041675+00:00
-- url     : https://prove2.me/theorems/7d4e8ef5-2c7c-47d2-93eb-cfca46d77c15
-- title:
--   Proof of Theorem 1: $y(p)$ consists of maximizers over $\overline{\operatorname{conv}}\,\operatorname{Im}(y)$
-- statement:
--   Let $y:\mathbb R^N\rightrightarrows\mathbb R^N$ be a supply correspondence that satisfies the law of supply and is homogeneous of degree $0$. Let $Y=\overline{\operatorname{conv}}\,\operatorname{Im}(y)$ be the closure of the convex hull of the image of $y$. Then for every $p$,
--
--   $$y(p)\ \subseteq\ \{z\in Y\mid p\cdot z=\sup_{z'\in Y}p\cdot z'\}.$$
--
--   If $y$ is empty-valued everywhere, $Y=\emptyset$ and the inclusion is trivial. This identifies the production set that rationalizes $y$ in Theorem 1 and is reused in the sufficiency part of Theorem 2.
--
--   Differences from the source:
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
--   - encoding: z ∈ Y with p · z = sup_{z′∈Y} p · z′ → z ∈ Y ∧ ∀ z′ ∈ Y, p ⬝ᵥ z′ ≤ p ⬝ᵥ z (optSet); reason: for z ∈ Y the two are equivalent (the supremum taken in the extended reals); avoids Lean's real sSup, which is 0 on unbounded sets
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, proof of Theorem 1, second paragraph, p.5

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, proof of Theorem 1, second paragraph, p.5: if `y`
satisfies the law of supply and is homogeneous of degree zero and `Y` is the closure of the
convex hull of `Im(y)`, then `y(p) ⊆ {z ∈ Y | p · z = sup_{z′∈Y} p · z′}` for every `p`.

Formalization Note: the optimal set is `optSet` (`z ∈ Y` and `p · z ≥ p · z′` for all
`z′ ∈ Y`). If `Im(y) = ∅` then `Y = ∅` and the claim is vacuous (every `y p` is empty). -/
theorem theorem_1_subset_opt_closure_hull {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ))
    (hsup : LawOfSupply y) (hhom : IsHomogeneousZero y) :
    ∀ p, y p ⊆ optSet (closure (convexHull ℝ (image y))) p := by sorry

end SupplyCorr
