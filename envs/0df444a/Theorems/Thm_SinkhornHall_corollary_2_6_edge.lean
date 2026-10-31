-- Prove2me | Theorems.Thm_SinkhornHall_corollary_2_6_edge
-- name    : SinkhornHall.corollary_2_6_edge
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:24.203995+00:00
-- url     : https://prove2.me/theorems/c1ac3b85-ad78-4017-b57e-88a41bab941c
-- title:
--   Corollary 2.6, second sentence — $\kappa(x,y)\le A_{\min}$ forces $x_ky_\ell<\prod_i x_i^{r_i/R}\prod_j y_j^{c_j/C}$ on every edge (corrected: at least two positive entries)
-- statement:
--   Let $A$ be a nonnegative matrix with neither zero rows nor zero columns and at least two positive entries, $r,c$ positive marginals with $R=C$, and $x,y$ positive scaling vectors with $\kappa(x,y)\le A_{\min}$. Then for every $k,\ell$ with $A_{k\ell}>0$,
--
--   $$x_ky_\ell\ <\ \prod_i x_i^{r_i/R}\prod_j y_j^{c_j/C}.$$
--
--   With $(r,c)=(\mathbf 1,\mathbf 1)$ this reads $x_iy_j<(x_1\cdots x_ny_1\cdots y_n)^{1/n}$ on every edge, the input of the rounding step of Theorem 4.1.
--
--   Differences from the source:
--   - correction: Corollary 2.6 for every A satisfying §2's assumptions → adds 1 < numEdges A (at least two positive entries); reason: the corollary specializes Lemma 2.5, stated for m ≥ 2 terms (one per positive entry); for the 1 × 1 matrix A = (1), r = c = (1), κ ≡ 1 = A_min, yet A is scalable and x₁y₁ < x₁y₁ fails, so both sentences are false; with no zero rows and columns the hypothesis excludes exactly the 1 × 1 case
--   - reading: §2 standing assumptions (p.4): A nonnegative with neither zero rows nor zero columns, r and c positive vectors → hypotheses hA, hrow, hcol, hr, hc; reason: stated once at the top of §2
--   - reading: §2.1 standing assumption (p.6): R = C → hypothesis hRC : Σ r = Σ c; reason: assumed throughout §2.1
--   - encoding: index sets [n], [m] → finite types ι, κ; reason: 1 < numEdges A forces both to be nonempty
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Corollary 2.6, second sentence, p.7

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **Corollary 2.6, second sentence.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Corollary 2.6, p.7: "For such x, y [scaling vectors with
κ(x, y) ≤ A_min], it holds x_k y_ℓ < ∏_i x_i^{r_i/R} ∏_j y_j^{c_j/C} (∀k, ℓ : A_kℓ > 0)."

Setting of §2 and §2.1: `A` nonnegative with neither zero rows nor zero columns, `r`, `c` positive,
`R = C`.

**Correction.** The corollary is obtained by "specializing Lemma 2.5 to (2.4)", and Lemma 2.5 is
stated for `m ≥ 2` terms, one per positive entry of `A`. With a single positive entry the printed
statement is false: for the `1 × 1` matrix `A = (1)` with `r = c = (1)` one has `κ(x, y) = 1 = A_min`
for all `x, y > 0`, although `A` is `(1, 1)`-scalable and `x₁y₁ < x₁y₁` fails. The hypothesis
`1 < numEdges A` (at least two positive entries, i.e. at least two terms in (2.4)) restores it. Under
no zero rows and columns this excludes exactly the `1 × 1` case.

**Formalization Note.** Powers are `Real.rpow` on positive bases; `R = Σ r`, `C = Σ c`. `Amin A` is
the least positive entry (`A` has one, by `1 < numEdges A`). Scaling vectors are positive. -/
theorem corollary_2_6_edge {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (h2 : 1 < numEdges A)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hRC : ∑ i, r i = ∑ j, c j) (x : ι → ℝ) (y : κ → ℝ) (hx : ∀ i, 0 < x i)
    (hy : ∀ j, 0 < y j) (hκ : kappa A r c x y ≤ Amin A) :
    ∀ k l, 0 < A k l →
      x k * y l < (∏ i, x i ^ (r i / ∑ i', r i')) * ∏ j, y j ^ (c j / ∑ j', c j') := by sorry

end SinkhornHall
