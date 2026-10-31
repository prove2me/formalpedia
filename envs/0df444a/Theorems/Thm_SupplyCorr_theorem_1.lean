-- Prove2me | Theorems.Thm_SupplyCorr_theorem_1
-- name    : SupplyCorr.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:51.171544+00:00
-- url     : https://prove2.me/theorems/761462d8-55d9-4a58-9b67-c343101496c7
-- title:
--   Theorem 1: the law of supply and homogeneity imply rationalizability (Definition 1 with $z\in Y$, $Y\neq\emptyset$)
-- statement:
--   A supply correspondence $y:\mathbb R^N\rightrightarrows\mathbb R^N$ that satisfies the law of supply and is homogeneous of degree $0$ is **rationalizable**: there is a nonempty, convex and closed production set $Y\subseteq\mathbb R^N$ such that for every price vector $p$,
--
--   $$y(p)\ \subseteq\ \{z\in Y\mid p\cdot z=\sup_{z'\in Y}p\cdot z'\}.$$
--
--   Theorem 1 is the paper's sufficient condition for plain rationalizability, and its proof constructs the set $Y$ used for Theorem 2.
--
--   Differences from the source:
--   - generalization: Definition 1 (p.3): y(p) ⊆ {z ∈ ℝᴺ | p · z = sup_{z′∈Y} p · z′} for some convex closed Y → y(p) ⊆ {z ∈ Y | p · z = sup_{z′∈Y} p · z′} for some nonempty convex closed Y; reason: the Lean conclusion implies the printed one (a maximizer z ∈ Y satisfies p · z = sup); it is the form proved on p.5, and it keeps Definitions 1 and 2 uniform
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
--   - encoding: z ∈ Y with p · z = sup_{z′∈Y} p · z′ → z ∈ Y ∧ ∀ z′ ∈ Y, p ⬝ᵥ z′ ≤ p ⬝ᵥ z (optSet); reason: for z ∈ Y the two are equivalent (the supremum taken in the extended reals); avoids Lean's real sSup, which is 0 on unbounded sets
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, Theorem 1, p.4

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, Theorem 1, p.4: a correspondence
`y : ℝᴺ ⇒ ℝᴺ` is rationalizable if it satisfies the law of supply and is homogeneous of degree
zero.

Formalization Note: rationalizability is the corrected Definition 1 (`IsRationalizable`): a
nonempty closed convex `Y` with `y(p) ⊆ {z ∈ Y | p · z = sup_{z′∈Y} p · z′}`; this is stronger
than the printed `{z ∈ ℝᴺ | …}`. `ℝᴺ` is `Fin N → ℝ`, for every `N`. -/
theorem theorem_1 {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ))
    (hsup : LawOfSupply y) (hhom : IsHomogeneousZero y) :
    IsRationalizable y := by sorry

end SupplyCorr
