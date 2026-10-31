-- Prove2me | Theorems.Thm_SupplyCorr_theorem_1_profit_const
-- name    : SupplyCorr.theorem_1_profit_const
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:41.112718+00:00
-- url     : https://prove2.me/theorems/f895e4ee-31c7-4637-93ab-2d4f18b17860
-- title:
--   Proof of Theorem 1: $p\cdot z$ is constant on $y(p)$
-- statement:
--   Let $y:\mathbb R^N\rightrightarrows\mathbb R^N$ be a supply correspondence that satisfies the law of supply and is homogeneous of degree $0$. Then for every price vector $p$ the profit $p\cdot z$ is the same for all plans in $y(p)$:
--
--   $$z,z'\in y(p)\ \Longrightarrow\ p\cdot z=p\cdot z'.$$
--
--   This is the first step of the proof of Theorem 1.
--
--   Differences from the source:
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, proof of Theorem 1, first paragraph, p.4

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, proof of Theorem 1, first paragraph, p.4: if `y`
satisfies the law of supply and is homogeneous of degree zero, then `p · z` is constant over
`z ∈ y(p)`.

Formalization Note: `ℝᴺ` is `Fin N → ℝ` with `⬝ᵥ`, for every `N`. -/
theorem theorem_1_profit_const {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ))
    (hsup : LawOfSupply y) (hhom : IsHomogeneousZero y) :
    ∀ (p z z' : Fin N → ℝ), z ∈ y p → z' ∈ y p → p ⬝ᵥ z = p ⬝ᵥ z' := by sorry

end SupplyCorr
