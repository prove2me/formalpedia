-- Prove2me | Theorems.Thm_SupplyCorr_theorem_1_weak_axiom
-- name    : SupplyCorr.theorem_1_weak_axiom
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:43.847732+00:00
-- url     : https://prove2.me/theorems/e70f40a2-3e04-437c-a516-19773c73e433
-- title:
--   Proof of Theorem 1: the weak axiom of profit maximization
-- statement:
--   Let $y:\mathbb R^N\rightrightarrows\mathbb R^N$ be a supply correspondence that satisfies the law of supply and is homogeneous of degree $0$. Then $y$ satisfies the **weak axiom of profit maximization**: for all price vectors $p,p'$ and plans $z\in y(p)$, $z'\in y(p')$,
--
--   $$p\cdot z\ \ge\ p\cdot z'.$$
--
--   Every plan chosen at prices $p$ earns at least as much at $p$ as any plan chosen at other prices; this is the core of Theorem 1.
--
--   Differences from the source:
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, proof of Theorem 1, display (1), pp.4–5

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, proof of Theorem 1, (1), pp.4–5: if `y`
satisfies the law of supply and is homogeneous of degree zero, it satisfies the weak axiom of
profit maximization: `p · z ≥ p · z′` for all `p, p′ ∈ ℝᴺ`, `z ∈ y(p)`, `z′ ∈ y(p′)`.

Formalization Note: `ℝᴺ` is `Fin N → ℝ` with `⬝ᵥ`, for every `N`. -/
theorem theorem_1_weak_axiom {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ))
    (hsup : LawOfSupply y) (hhom : IsHomogeneousZero y) :
    ∀ (p p' z z' : Fin N → ℝ), z ∈ y p → z' ∈ y p' → p ⬝ᵥ z' ≤ p ⬝ᵥ z := by sorry

end SupplyCorr
