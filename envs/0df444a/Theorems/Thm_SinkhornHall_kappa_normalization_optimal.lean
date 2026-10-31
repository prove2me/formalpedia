-- Prove2me | Theorems.Thm_SinkhornHall_kappa_normalization_optimal
-- name    : SinkhornHall.kappa_normalization_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:09.975399+00:00
-- url     : https://prove2.me/theorems/84006bc6-d0a9-40b5-9057-53889cb844aa
-- title:
--   §2.1 — $R(y)$ minimizes $\kappa(\cdot,y)$ and $C(x)$ minimizes $\kappa(x,\cdot)$
-- statement:
--   Let $A$ be a nonnegative matrix with neither zero rows nor zero columns, $r,c$ positive marginals with $R=C$, and $\kappa$ the capacity (2.2). For all positive vectors $x,y$:
--
--   $$\kappa\big(R(y),y\big)\le\kappa(x,y)\qquad\text{and}\qquad\kappa\big(x,C(x)\big)\le\kappa(x,y).$$
--
--   So, with one block fixed, the row- (column-) normalization vector is an optimal value of the other block, and the Sinkhorn algorithm is alternating minimization of $\kappa$. In the proof of Theorem 4.1 this gives $\kappa(\mathbf 1,C(\mathbf 1))\le\kappa(\mathbf 1,\mathbf 1)$, the starting value of the iteration bound.
--
--   Differences from the source:
--   - reading: 'an optimal x is given by R(y)' (and likewise C(x)) → κ(R(y), y) ≤ κ(x, y) and κ(x, C(x)) ≤ κ(x, y) for all positive x, y; reason: optimality for the minimization (2.2) over positive vectors
--   - reading: §2 standing assumptions (p.4): A nonnegative with neither zero rows nor zero columns, r and c positive vectors, [n] for a positive integer n → hypotheses hA, hrow, hcol, hr, hc and a nonempty row index type; reason: these are stated once at the top of §2 and apply to every result of the section
--   - reading: §2.1 standing assumption (p.6): R = C → hypothesis hRC : Σ r = Σ c; reason: assumed throughout §2.1
--   - encoding: index sets [n] and [m] → finite types ι and κ (ι nonempty); reason: any finite type is in bijection with some [n]; no instance changes
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, §2.1, after (2.2), p.6 (unnumbered)

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **`R(y)` and `C(x)` are the partial minimizers of `κ`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2.1, after (2.2), p.6: "Fixing y, an optimal x is given
by row-normalization vector R(y). Also, fixing x, an optimal y is given by column-normalization
vector C(x)."

Setting of §2 and §2.1: `A` nonnegative with neither zero rows nor zero columns, `r`, `c` positive,
`R = C`. Both clauses: `κ(R(y), y) ≤ κ(x, y)` and `κ(x, C(x)) ≤ κ(x, y)` for all positive `x`, `y`.

**Formalization Note.** "Optimal" for the minimization (2.2) over positive vectors is stated as
"no larger than `κ` at any other positive vector"; `R(y)` and `C(x)` are themselves positive under
these hypotheses.

Row and column indices are finite types `ι`, `κ` with `ι` nonempty (the paper's `[n]`, `[m]`
for positive integers `n`, `m`, p.4; `κ` is then nonempty because `A` has no zero row). -/
theorem kappa_normalization_optimal {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hRC : ∑ i, r i = ∑ j, c j) (x : ι → ℝ) (y : κ → ℝ) (hx : ∀ i, 0 < x i)
    (hy : ∀ j, 0 < y j) :
    kappa A r c (rowNorm A r y) y ≤ kappa A r c x y ∧
      kappa A r c x (colNorm A c x) ≤ kappa A r c x y := by sorry

end SinkhornHall
