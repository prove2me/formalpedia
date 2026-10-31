-- Prove2me | Theorems.Thm_SinkhornHall_theorem_2_3_2
-- name    : SinkhornHall.theorem_2_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:35.217781+00:00
-- url     : https://prove2.me/theorems/eb98497b-7449-4c97-9329-9409da294b61
-- title:
--   Theorem 2.3 (2) — approximate $(r,c)$-scalability iff $\inf\kappa>0$
-- statement:
--   Let $A$ be a nonnegative $n\times m$ matrix with neither zero rows nor zero columns and $r,c$ positive marginals with $R=C$. Then $A$ is approximately $(r,c)$-scalable if and only if
--
--   $$\inf_{x,y>0}\kappa(x,y)\ >\ 0 .$$
--
--   This classical result of Rothblum and Schneider is the bridge between the analytic potential $\kappa$ and scalability; it gives the first sentence of Corollary 2.6.
--
--   **Formalization Note** $\inf\kappa>0$ is stated as: some $\delta>0$ is a lower bound of $\kappa$ on positive vectors. Approximate scalability uses the $\ell_1$ norm.
--
--   Differences from the source:
--   - encoding: inf_{x,y} κ(x, y) > 0 → ∃ δ > 0, ∀ positive x, y, δ ≤ κ(x, y); reason: equivalent: the infimum of a set of positive reals is > 0 iff it has a positive lower bound
--   - encoding: 'arbitrarily close … under some norm of ℝ^{n+m}' → ℓ₁ error < ε for every ε > 0; reason: all norms on ℝ^{n+m} are equivalent
--   - reading: §2 standing assumptions (p.4): A nonnegative with neither zero rows nor zero columns, r and c positive vectors, [n] for a positive integer n → hypotheses hA, hrow, hcol, hr, hc and a nonempty row index type; reason: these are stated once at the top of §2 and apply to every result of the section
--   - reading: §2.1 standing assumption (p.6): R = C → hypothesis hRC : Σ r = Σ c; reason: assumed throughout §2.1
--   - encoding: index sets [n] and [m] → finite types ι and κ (ι nonempty); reason: any finite type is in bijection with some [n]; no instance changes
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Theorem 2.3 (2), p.6 (cited from [27])

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **Theorem 2.3 (2)** (Rothblum–Schneider [27]).
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Theorem 2.3 (2), p.6: "A is approximately
(r, c)-scalable if and only if inf_{x,y} κ(x, y) > 0."

Setting of §2 and §2.1: `A` a nonnegative matrix with neither zero rows nor zero columns, `r`, `c`
positive vectors, `R = C`; the infimum is over positive `x`, `y` ((2.2), p.6).

**Formalization Note.** `inf_{x,y} κ(x, y) > 0` is encoded as the existence of `δ > 0` with
`δ ≤ κ(x, y)` for all positive `x`, `y` (equivalent, since `κ > 0` on positive vectors).
Approximate scalability is `ApproxScalable` (`ℓ₁` norm). The row index set is nonempty (the paper's
`[n]` for a positive integer `n`, p.4). -/
theorem theorem_2_3_2 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hRC : ∑ i, r i = ∑ j, c j) :
    ApproxScalable A r c ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ι → ℝ) (y : κ → ℝ), (∀ i, 0 < x i) → (∀ j, 0 < y j) →
        δ ≤ kappa A r c x y := by sorry

end SinkhornHall
