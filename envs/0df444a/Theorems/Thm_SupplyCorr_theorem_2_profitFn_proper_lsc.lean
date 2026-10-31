-- Prove2me | Theorems.Thm_SupplyCorr_theorem_2_profitFn_proper_lsc
-- name    : SupplyCorr.theorem_2_profitFn_proper_lsc
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:51.288739+00:00
-- url     : https://prove2.me/theorems/fa654f37-f351-4a8b-be84-e1d72be3d394
-- title:
--   Proof of Theorem 2, necessity: the profit function is proper, lower semicontinuous and convex (corrected: $Y\neq\emptyset$)
-- statement:
--   Let $Y\subseteq\mathbb R^N$ be nonempty. Its profit (support) function $\pi(p)=\sup_{z'\in Y}p\cdot z'$, with values in $(-\infty,+\infty]$, is a **proper convex** function (it never equals $-\infty$, it is finite somewhere, and $\pi((1-t)p+tq)\le(1-t)\pi(p)+t\pi(q)$ for $0<t<1$) and it is **lower semicontinuous**.
--
--   This is the hypothesis under which the paper applies the maximal monotonicity of subdifferentials (Rockafellar's theorem).
--
--   Differences from the source:
--   - generalization: Y convex and closed → Y only nonempty; reason: a supremum of linear functions is convex and lower semicontinuous for every Y; nonempty convex closed Y are a special case
--   - correction: Definition 2 (p.3): a convex and closed production set Y → Y nonempty; reason: Y = ∅ strongly rationalizes y ≡ ∅, which is homogeneous but not maximal monotone (its empty graph lies strictly inside the monotone set {(0,0)}); the necessity proof calls π proper, which needs Y ≠ ∅
--   - generalization: N ≥ 2 commodities (§2, p.3) → every N : ℕ; reason: no step of the argument uses N ≥ 2; the case N ≥ 2 is a special case of the Lean statement
--   - encoding: ℝᴺ with the scalar product p · z → Fin N → ℝ with the dot product ⬝ᵥ; reason: Lean representation of ℝᴺ; same instances
--   - encoding: proper lower semicontinuous convex function → RockafellarMaxMono.Shared.ProperConvex (platform definition, EReal-valued) ∧ LowerSemicontinuous; reason: the platform's standard notion of a proper convex function (never −∞, not identically +∞, convexity inequality in EReal); same instances
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, proof of Theorem 2, necessity, p.6

import Mathlib
import Definitions.Def_SupplyCorr_Model
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, proof of Theorem 2, necessity, p.6: the profit
function `π(p) = sup_{z′∈Y} p · z′` is a proper lower semicontinuous convex function, as the
support function of `Y`.

Formalization Note: stated for every nonempty `Y`; closedness and convexity of `Y` are not
needed. Properness and convexity are the platform definition
`RockafellarMaxMono.Shared.ProperConvex` (never `−∞`, somewhere finite, convexity inequality in
`EReal`). -/
theorem theorem_2_profitFn_proper_lsc {N : ℕ} (Y : Set (Fin N → ℝ)) (hne : Y.Nonempty) :
    RockafellarMaxMono.Shared.ProperConvex (profitFn Y) ∧
      LowerSemicontinuous (profitFn Y) := by sorry

end SupplyCorr
