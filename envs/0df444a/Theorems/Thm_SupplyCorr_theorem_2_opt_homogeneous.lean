-- Prove2me | Theorems.Thm_SupplyCorr_theorem_2_opt_homogeneous
-- name    : SupplyCorr.theorem_2_opt_homogeneous
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:28:18.952398+00:00
-- url     : https://prove2.me/theorems/a9eba231-841d-401a-b779-400309ee8c1a
-- title:
--   Proof of Theorem 2, necessity: the optimal-plan correspondence is homogeneous of degree $0$
-- statement:
--   Let $Y\subseteq\mathbb R^N$ be any set. For every price vector $p$ and every $\lambda>0$,
--
--   $$\{z\in Y\mid \lambda p\cdot z=\sup_{z'\in Y}\lambda p\cdot z'\}=\{z\in Y\mid p\cdot z=\sup_{z'\in Y}p\cdot z'\},$$
--
--   so the optimal-plan correspondence of $Y$ is homogeneous of degree $0$. This is the second half of the "only if" direction of Theorem 2.
--
--   Differences from the source:
--   - generalization: Y convex and closed (the production set of a strongly rationalizable y) → any Y ⊆ ℝᴺ; reason: scaling prices by λ > 0 does not change the maximizers for any set Y; the source's Y is a special case
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
--   - encoding: z ∈ Y with p · z = sup_{z′∈Y} p · z′ → z ∈ Y ∧ ∀ z′ ∈ Y, p ⬝ᵥ z′ ≤ p ⬝ᵥ z (optSet); reason: for z ∈ Y the two are equivalent (the supremum taken in the extended reals); avoids Lean's real sSup, which is 0 on unbounded sets
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, proof of Theorem 2, necessity, last display, p.6

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, proof of Theorem 2, necessity, last display,
p.6: for any scalar `λ > 0`, `{z ∈ Y : p · z = sup_{z′∈Y} p · z′} = {z ∈ Y : λp · z =
sup_{z′∈Y} λp · z′}`, so the optimal-plan correspondence is homogeneous of degree zero.

Formalization Note: stated for every `Y ⊆ ℝᴺ`; no hypothesis on `Y` is needed. -/
theorem theorem_2_opt_homogeneous {N : ℕ} (Y : Set (Fin N → ℝ)) :
    IsHomogeneousZero (optSet Y) := by sorry

end SupplyCorr
