-- Prove2me | Theorems.Thm_SupplyCorr_theorem_2_opt_eq_subdiff
-- name    : SupplyCorr.theorem_2_opt_eq_subdiff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:42.804786+00:00
-- url     : https://prove2.me/theorems/31898f07-e044-4acb-8266-0fbfd96a98a5
-- title:
--   Proof of Theorem 2, necessity: the optimal-plan correspondence equals $\partial\pi$ (corrected: $z\in Y$, $Y\neq\emptyset$)
-- statement:
--   Let $Y\subseteq\mathbb R^N$ be nonempty, convex and closed, and let $\pi(p)=\sup_{z'\in Y}p\cdot z'\in(-\infty,+\infty]$ be its profit (support) function. Then for every price vector $p$,
--
--   $$\{z\in Y\mid p\cdot z=\sup_{z'\in Y}p\cdot z'\}=\partial\pi(p)=\{z\in\mathbb R^N\mid \pi(q)\ge\pi(p)+(q-p)\cdot z\ \text{for all } q\}.$$
--
--   So a strongly rationalizable correspondence is the subdifferential of the profit function, which is how the paper derives maximal monotonicity.
--
--   Differences from the source:
--   - correction: Definition 2 (p.3): y(p) = {z ∈ ℝᴺ | p · z = sup_{z′∈Y} p · z′} → y(p) = {z ∈ Y | p · z = sup_{z′∈Y} p · z′} (optSet Y p); reason: the printed set is a hyperplane and makes Theorem 2 false: N = 2, Y = {0} gives y(p) = {z | p · z = 0}, and p = (1,0), z = (0,1), p′ = (0,1), z′ = (1,0) give (p − p′)·(z − z′) = −2 < 0, so y is not monotone; the proofs on pp.5–6 use z ∈ Y
--   - correction: Definition 2 (p.3): a convex and closed production set Y → a nonempty convex and closed Y; reason: Y = ∅ strongly rationalizes y ≡ ∅, which is homogeneous but not maximal monotone (its empty graph lies strictly inside the monotone set {(0,0)}); the necessity proof calls π proper, which needs Y ≠ ∅
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
--   - encoding: z ∈ Y with p · z = sup_{z′∈Y} p · z′ → z ∈ Y ∧ ∀ z′ ∈ Y, p ⬝ᵥ z′ ≤ p ⬝ᵥ z (optSet); reason: for z ∈ Y the two are equivalent (the supremum taken in the extended reals); avoids Lean's real sSup, which is 0 on unbounded sets
--   - encoding: π(p) = sup_{z′∈Y} p · z′ and the subdifferential ∂π → profitFn Y valued in EReal; subdiffDot with the dot-product pairing; reason: π may be +∞; extended reals keep that value, and identifying ℝᴺ with its dual by the dot product makes ∂π a correspondence ℝᴺ ⇒ ℝᴺ like y
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, proof of Theorem 2, necessity, p.6

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, proof of Theorem 2, necessity, p.6: for a
nonempty closed convex production set `Y`, the optimal-plan correspondence
`p ↦ {z ∈ Y | p · z = sup_{z′∈Y} p · z′}` is the subdifferential `∂π` of the profit function
`π(p) = sup_{z′∈Y} p · z′`.

Formalization Note: `π` is `profitFn Y : ℝᴺ → EReal`; `∂` is `subdiffDot`, the subdifferential
with the dot-product pairing. `Y` nonempty is needed: for `Y = ∅`, `π ≡ −∞` and `∂π(p) = ℝᴺ`. -/
theorem theorem_2_opt_eq_subdiff {N : ℕ} (Y : Set (Fin N → ℝ))
    (hne : Y.Nonempty) (hconv : Convex ℝ Y) (hclosed : IsClosed Y) :
    ∀ p, optSet Y p = subdiffDot (profitFn Y) p := by sorry

end SupplyCorr
