-- Prove2me | Theorems.Thm_SupplyCorr_theorem_2_sufficiency
-- name    : SupplyCorr.theorem_2_sufficiency
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:58.159223+00:00
-- url     : https://prove2.me/theorems/fc9ca3c7-b050-4919-a49f-cd46c9e6bae6
-- title:
--   Proof of Theorem 2, sufficiency: $y=\operatorname{opt}$ over $\overline{\operatorname{conv}}\,\operatorname{Im}(y)$ (corrected: $z\in Y$, $Y\ne\emptyset$)
-- statement:
--   Let $y:\mathbb R^N\rightrightarrows\mathbb R^N$ be maximal monotone and homogeneous of degree $0$, and let $Y=\overline{\operatorname{conv}}\,\operatorname{Im}(y)$. Then $Y$ is nonempty and for every price vector $p$,
--
--   $$y(p)=\{z\in Y\mid p\cdot z=\sup_{z'\in Y}p\cdot z'\}.$$
--
--   Since $Y$ is closed and convex, this is the "if" direction of Theorem 2.
--
--   Differences from the source:
--   - correction: Definition 2 (p.3): y(p) = {z ∈ ℝᴺ | p · z = sup_{z′∈Y} p · z′} → y(p) = {z ∈ Y | p · z = sup_{z′∈Y} p · z′} (optSet Y p); reason: the printed set is a hyperplane and makes Theorem 2 false: N = 2, Y = {0} gives y(p) = {z | p · z = 0}, and p = (1,0), z = (0,1), p′ = (0,1), z′ = (1,0) give (p − p′)·(z − z′) = −2 < 0, so y is not monotone; the proofs on pp.5–6 use z ∈ Y
--   - correction: (no nonemptiness claim) → the conclusion also asserts that Y = cl conv Im(y) is nonempty; reason: the corrected Definition 2 requires Y ≠ ∅ (Y = ∅ strongly rationalizes y ≡ ∅, which is not maximal monotone); a maximal monotone graph is nonempty, so this conjunct is what the corrected Definition 2 needs
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
--   - encoding: z ∈ Y with p · z = sup_{z′∈Y} p · z′ → z ∈ Y ∧ ∀ z′ ∈ Y, p ⬝ᵥ z′ ≤ p ⬝ᵥ z (optSet); reason: for z ∈ Y the two are equivalent (the supremum taken in the extended reals); avoids Lean's real sSup, which is 0 on unbounded sets
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, proof of Theorem 2, sufficiency, p.5

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, proof of Theorem 2, sufficiency, p.5: if `y` is
maximal monotone and homogeneous of degree zero and `Y` is the closure of the convex hull of
`Im(y)`, then `Y` is nonempty and `y(p) = {z ∈ Y | p · z = sup_{z′∈Y} p · z′}` for every `p`.

Formalization Note: the printed set `{z ∈ ℝᴺ | …}` is read with `z ∈ Y` (Correction 1); the
nonemptiness of `Y` is the conjunct needed by the corrected Definition 2 (Correction 2). -/
theorem theorem_2_sufficiency {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ))
    (hmax : IsMaximalMonotone y) (hhom : IsHomogeneousZero y) :
    (closure (convexHull ℝ (image y))).Nonempty ∧
      ∀ p, y p = optSet (closure (convexHull ℝ (image y))) p := by sorry

end SupplyCorr
