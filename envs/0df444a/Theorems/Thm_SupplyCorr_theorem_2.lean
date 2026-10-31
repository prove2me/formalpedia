-- Prove2me | Theorems.Thm_SupplyCorr_theorem_2
-- name    : SupplyCorr.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:12.667057+00:00
-- url     : https://prove2.me/theorems/b8891265-15e7-4b46-ba8d-d8df033fb5f6
-- title:
--   Theorem 2: strongly rationalizable iff maximal monotone and homogeneous of degree zero (corrected: Definition 2 reads $z\in Y$ and $Y\neq\emptyset$)
-- statement:
--   Let $N\ge 0$ and let $y:\mathbb R^N\rightrightarrows\mathbb R^N$ be any supply correspondence (empty values allowed). Then $y$ is **strongly rationalizable**, i.e. there is a nonempty, convex and closed production set $Y\subseteq\mathbb R^N$ with
--
--   $$y(p)=\{z\in Y\mid p\cdot z=\sup_{z'\in Y}p\cdot z'\}\qquad\text{for every } p\in\mathbb R^N,$$
--
--   **if and only if** $y$ is **maximal monotone** (its graph $\{(z,p): z\in y(p)\}$ is monotone, $(z-z')\cdot(p-p')\ge 0$, and is maximal among all monotone subsets of $\mathbb R^N\times\mathbb R^N$) and **homogeneous of degree $0$** ($y(\lambda p)=y(p)$ for all $p$ and $\lambda>0$).
--
--   This characterizes the supply behaviour of a profit-maximizing competitive firm with a closed convex technology without differentiability, finiteness of the image or cyclic monotonicity.
--
--   Differences from the source:
--   - correction: Definition 2 (p.3): y(p) = {z ∈ ℝᴺ | p · z = sup_{z′∈Y} p · z′} → y(p) = {z ∈ Y | p · z = sup_{z′∈Y} p · z′} (optSet Y p); reason: the printed set is a hyperplane and makes Theorem 2 false: N = 2, Y = {0} gives y(p) = {z | p · z = 0}, and p = (1,0), z = (0,1), p′ = (0,1), z′ = (1,0) give (p − p′)·(z − z′) = −2 < 0, so y is not monotone; the proofs on pp.5–6 use z ∈ Y
--   - correction: Definition 2 (p.3): a convex and closed production set Y → a nonempty convex and closed Y; reason: Y = ∅ strongly rationalizes y ≡ ∅, which is homogeneous but not maximal monotone (its empty graph lies strictly inside the monotone set {(0,0)}); the necessity proof calls π proper, which needs Y ≠ ∅
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
--   - encoding: z ∈ Y with p · z = sup_{z′∈Y} p · z′ → z ∈ Y ∧ ∀ z′ ∈ Y, p ⬝ᵥ z′ ≤ p ⬝ᵥ z (optSet); reason: for z ∈ Y the two are equivalent (the supremum taken in the extended reals); avoids Lean's real sSup, which is 0 on unbounded sets
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, Theorem 2, p.5 (proof pp.5–6)

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, Theorem 2, p.5: a correspondence
`y : ℝᴺ ⇒ ℝᴺ` is strongly rationalizable if and only if it is maximal monotone and homogeneous
of degree zero.

Formalization Note: `ℝᴺ` is `Fin N → ℝ` with the dot product, for every `N` (the paper assumes
`N ≥ 2`); `y` is arbitrary and may take empty values. Strong rationalizability is the corrected
Definition 2: a nonempty closed convex `Y` with `y(p) = {z ∈ Y | p · z = sup_{z′∈Y} p · z′}`
for all `p` (the printed set `{z ∈ ℝᴺ | …}` is a hyperplane, and `Y = ∅` must be excluded).
Maximal monotonicity is against every monotone subset of `ℝᴺ × ℝᴺ`. -/
theorem theorem_2 {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ)) :
    IsStronglyRationalizable y ↔ IsMaximalMonotone y ∧ IsHomogeneousZero y := by sorry

end SupplyCorr
