-- Prove2me | Theorems.Thm_SinkhornHall_lemma_2_4
-- name    : SinkhornHall.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:14.787355+00:00
-- url     : https://prove2.me/theorems/efea69cf-5c61-4325-843c-5746a402a43f
-- title:
--   Lemma 2.4 — exact decrement of $\log\kappa$ in one row-and-column normalization
-- statement:
--   Let $A$ be a nonnegative matrix with neither zero rows nor zero columns, $r,c$ positive marginals with $R=C$, and $\kappa$ the capacity (2.2). For a positive vector $x$ put $y=C(x)$, $x'=R(y)$, $y'=C(x')$, and
--   $$p_i=\sum_j A_{ij}x_iy_j,\qquad q_j=\sum_i A_{ij}x'_iy_j .$$
--   Then
--
--   $$\log\kappa(x',y')-\log\kappa(x,y)\ =\ -\frac{D(r\|p)}{R}-\frac{D(c\|q)}{C}.$$
--
--   The identity expresses one Sinkhorn iteration as a decrease of the potential $\log\kappa$ by two KL divergences between the target and current marginals; combined with Pinsker's inequality it yields the iteration bound of Theorem 4.1.
--
--   **Formalization Note** The identity is stated in `EReal`; $p$ and $q$ are positive here, so both divergences are finite.
--
--   Differences from the source:
--   - reading: §2 standing assumptions (p.4): A nonnegative with neither zero rows nor zero columns, r and c positive vectors, [n] for a positive integer n → hypotheses hA, hrow, hcol, hr, hc and a nonempty row index type; reason: these are stated once at the top of §2 and apply to every result of the section
--   - reading: §2.1 standing assumption (p.6): R = C → hypothesis hRC : Σ r = Σ c; reason: assumed throughout §2.1
--   - encoding: real identity of (2.3) → the same identity in EReal, with klDiv; reason: p and q are positive, so both divergences are finite reals
--   - encoding: index sets [n] and [m] → finite types ι and κ (ι nonempty); reason: any finite type is in bijection with some [n]; no instance changes
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 2.4, (2.3), p.6

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **Lemma 2.4.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 2.4, (2.3), p.6: "Let y = C(x), x′ := R(y), and
y′ := C(x′). Then it holds log κ(x′, y′) − log κ(x, y) = −D(r∥p)/R − D(c∥q)/C, where
p_i := Σ_j A_ij x_i y_j and q_j := Σ_i A_ij x′_i y_j."

Setting of §2 and §2.1 (pp.4, 6): `A` nonnegative with neither zero rows nor zero columns, `r`, `c`
positive, and `R = C` (assumed throughout §2.1).

**Formalization Note.** `κ` is `kappa A r c`, `R(·)` is `rowNorm A r`, `C(·)` is `colNorm A c`,
`D` is `klDiv` (an `EReal`; here `p`, `q` are positive, so both divergences are finite), and the
identity is stated in `EReal`. `log` is `Real.log`.

Row and column indices are finite types `ι`, `κ` with `ι` nonempty (the paper's `[n]`, `[m]`
for positive integers `n`, `m`, p.4; `κ` is then nonempty because `A` has no zero row). -/
theorem lemma_2_4 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hRC : ∑ i, r i = ∑ j, c j) (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    let y := colNorm A c x
    let x' := rowNorm A r y
    let y' := colNorm A c x'
    let p : ι → ℝ := fun i => ∑ j, A i j * x i * y j
    let q : κ → ℝ := fun j => ∑ i, A i j * x' i * y j
    ((Real.log (kappa A r c x' y') - Real.log (kappa A r c x y) : ℝ) : EReal) =
      -(klDiv r p) / ((∑ i, r i : ℝ) : EReal) - klDiv c q / ((∑ j, c j : ℝ) : EReal) := by sorry

end SinkhornHall
