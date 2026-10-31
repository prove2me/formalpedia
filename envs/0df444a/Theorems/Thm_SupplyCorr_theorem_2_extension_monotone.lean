-- Prove2me | Theorems.Thm_SupplyCorr_theorem_2_extension_monotone
-- name    : SupplyCorr.theorem_2_extension_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:49.598667+00:00
-- url     : https://prove2.me/theorems/63cf1706-58cc-4aa1-b928-ca73ec2129d5
-- title:
--   Proof of Theorem 2: adding an optimal plan $(z^*,p^*)$ keeps the graph monotone (corrected: $z^*\in Y$)
-- statement:
--   Let $y:\mathbb R^N\rightrightarrows\mathbb R^N$ be a supply correspondence that satisfies the law of supply and is homogeneous of degree $0$. Let $Y=\overline{\operatorname{conv}}\,\operatorname{Im}(y)$, let $p^*$ be a price vector and let $z^*\in Y$ be optimal at $p^*$, i.e. $p^*\cdot z^*=\sup_{z'\in Y}p^*\cdot z'$. Then the graph of $y$ with the pair $(z^*,p^*)$ added is a monotone set:
--
--   $$(a-b)\cdot(q-q')\ge 0\quad\text{for all }(a,q),(b,q')\in G(y)\cup\{(z^*,p^*)\}.$$
--
--   If moreover $z^*\notin y(p^*)$, this set strictly includes $G(y)$. In the proof of Theorem 2 this is the extension that contradicts maximality.
--
--   Differences from the source:
--   - generalization: hypotheses: y maximal monotone and homogeneous; z* ∉ y(p*) → hypotheses: y satisfies the law of supply and is homogeneous; z* ∉ y(p*) kept only as the premise of the strict-inclusion clause; reason: maximal monotonicity implies the law of supply, which is all the argument uses; z* ∉ y(p*) is needed only for strictness, so the monotonicity clause holds without it, and adding it back gives the printed claim
--   - correction: p* · z* = sup_{z′∈Y} p · z′ (z* not required to lie in Y) → z* ∈ Y and p* · z′ ≤ p* · z* for all z′ ∈ Y; reason: the printed p is p*; without z* ∈ Y the claim is false: y ≡ {0} (Y = {0}), p* = (1,0), z* = (0,5) gives p* · z* = 0 = sup, but with (z′,p′) = (0,(0,1)) one gets (z* − z′)·(p* − p′) = −5 < 0; the argument uses p′ · (z′ − z*) ≥ 0, which needs z* ∈ Y (Correction 1)
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
--   - encoding: a new correspondence y′ with y′(p) = y(p) for p ≠ p* and y′(p*) = y(p*) ∪ z*, monotone, with graph strictly including that of y → IsMonotoneSet (graph y ∪ {(z*, p*)}) and graph y ⊂ graph y ∪ {(z*, p*)}; reason: graph y ∪ {(z*, p*)} is exactly G(y′), and maximality in Definition 4 is a statement about sets; same instances
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, proof of Theorem 2, sufficiency, second paragraph, p.5

import Mathlib
import Definitions.Def_SupplyCorr_Model

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, proof of Theorem 2, sufficiency, second
paragraph, p.5: let `y` satisfy the law of supply and be homogeneous of degree zero, let `Y` be
the closure of the convex hull of `Im(y)`, and let `z*` be an optimal plan in `Y` at prices `p*`.
Then the graph of `y` with the pair `(z*, p*)` added is a monotone set, and it strictly includes
the graph of `y` when `z* ∉ y(p*)`.

Formalization Note: the set `graph y ∪ {(z*, p*)}` is the graph of the paper's correspondence
`y′`. The paper assumes `z* ∉ y(p*)` throughout; it is needed only for the strict inclusion, so
it is the premise of that clause alone. `z* ∈ Y` is required (the printed `sup_{z′∈Y} p · z′`
reads `p* · z′`). The paper assumes `y` maximal monotone; only the law of supply it implies is
used. -/
theorem theorem_2_extension_monotone {N : ℕ} (y : (Fin N → ℝ) → Set (Fin N → ℝ))
    (hsup : LawOfSupply y) (hhom : IsHomogeneousZero y) (pstar zstar : Fin N → ℝ)
    (hopt : zstar ∈ optSet (closure (convexHull ℝ (image y))) pstar) :
    IsMonotoneSet (graph y ∪ {(zstar, pstar)}) ∧
      (zstar ∉ y pstar → graph y ⊂ graph y ∪ {(zstar, pstar)}) := by sorry

end SupplyCorr
