-- Prove2me | Theorems.Thm_SupplyCorr_theorem_2_opt_maximal_monotone
-- name    : SupplyCorr.theorem_2_opt_maximal_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:28:09.023802+00:00
-- url     : https://prove2.me/theorems/5d85c423-d67c-4e1e-89da-9b3749ad39d9
-- title:
--   Proof of Theorem 2, necessity: the optimal-plan correspondence of a nonempty closed convex $Y$ is maximal monotone (corrected: $z\in Y$, $Y\neq\emptyset$)
-- statement:
--   Let $Y\subseteq\mathbb R^N$ be nonempty, convex and closed. Then the optimal-plan correspondence
--
--   $$p\ \longmapsto\ \{z\in Y\mid p\cdot z=\sup_{z'\in Y}p\cdot z'\}$$
--
--   is **maximal monotone**: its graph $\{(z,p)\}$ is monotone, and it is not strictly contained in any monotone subset of $\mathbb R^N\times\mathbb R^N$.
--
--   The paper obtains this from $y=\partial\pi$ and the maximal monotonicity of subdifferentials of proper lower semicontinuous convex functions (Phelps, Theorem 2.15). It is the main half of the "only if" direction of Theorem 2.
--
--   Differences from the source:
--   - correction: Definition 2 (p.3): y(p) = {z ∈ ℝᴺ | p · z = sup_{z′∈Y} p · z′} → y(p) = {z ∈ Y | p · z = sup_{z′∈Y} p · z′} (optSet Y p); reason: the printed set is a hyperplane and makes Theorem 2 false: N = 2, Y = {0} gives y(p) = {z | p · z = 0}, and p = (1,0), z = (0,1), p′ = (0,1), z′ = (1,0) give (p − p′)·(z − z′) = −2 < 0, so y is not monotone; the proofs on pp.5–6 use z ∈ Y
--   - correction: Definition 2 (p.3): a convex and closed production set Y → a nonempty convex and closed Y; reason: Y = ∅ strongly rationalizes y ≡ ∅, which is homogeneous but not maximal monotone (its empty graph lies strictly inside the monotone set {(0,0)}); the necessity proof calls π proper, which needs Y ≠ ∅
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
--   - encoding: z ∈ Y with p · z = sup_{z′∈Y} p · z′ → z ∈ Y ∧ ∀ z′ ∈ Y, p ⬝ᵥ z′ ≤ p ⬝ᵥ z (optSet); reason: for z ∈ Y the two are equivalent (the supremum taken in the extended reals); avoids Lean's real sSup, which is 0 on unbounded sets
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, proof of Theorem 2, necessity, p.6

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, proof of Theorem 2, necessity, p.6: for a
nonempty closed convex production set `Y`, the optimal-plan correspondence
`p ↦ {z ∈ Y | p · z = sup_{z′∈Y} p · z′}` is maximal monotone (the paper cites Phelps 1997,
Theorem 2.15, via `y = ∂π`).

Formalization Note: maximality is against every monotone subset of `ℝᴺ × ℝᴺ`. -/
theorem theorem_2_opt_maximal_monotone {N : ℕ} (Y : Set (Fin N → ℝ))
    (hne : Y.Nonempty) (hconv : Convex ℝ Y) (hclosed : IsClosed Y) :
    IsMaximalMonotone (optSet Y) := by sorry

end SupplyCorr
