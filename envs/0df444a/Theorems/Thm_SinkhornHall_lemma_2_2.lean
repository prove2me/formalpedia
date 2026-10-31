-- Prove2me | Theorems.Thm_SinkhornHall_lemma_2_2
-- name    : SinkhornHall.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:10.124519+00:00
-- url     : https://prove2.me/theorems/453fcbb9-0f79-49c2-b7f1-3cf973d7665a
-- title:
--   Lemma 2.2 — the $\ell_1$ marginal error of any scaling is at least $2(\max_{X\sqcup Y}\, r(X)+c(Y) - (R+C)/2)$
-- statement:
--   Let $A$ be a nonnegative $n\times m$ matrix with neither zero rows nor zero columns, let $r\in\mathbb R^n$, $c\in\mathbb R^m$ be positive vectors with $R=r([n])$, $C=c([m])$ (here $R=C$ is not assumed), and let $\tilde A_{ij}=A_{ij}x_iy_j$ be any scaling of $A$ by positive vectors $x,y$. Then
--
--   $$\|\tilde A\mathbf 1-r\|_1+\|\tilde A^\top\mathbf 1-c\|_1\ \ge\ 2\Big(\max_{X\sqcup Y\in\mathcal S}\big(r(X)+c(Y)\big)-\frac{R+C}{2}\Big),$$
--
--   where $\mathcal S$ is the family of stable sets of the support graph $G(A)$. Equivalently: for every stable $X\sqcup Y$, the error is at least $2r(X)+2c(Y)-R-C$.
--
--   With $(r,c)=(\mathbf 1,\mathbf 1)$ and a Hall blocker $X$, the stable set $X\sqcup([n]\setminus\Gamma(X))$ makes the right side at least $2$; this is how the proof of Theorem 4.1 bounds the marginal error away from zero.
--
--   **Formalization Note** The maximum over the finite, nonempty family $\mathcal S$ is stated by quantifying over every stable pair $(X,Y)$ of row and column sets.
--
--   Differences from the source:
--   - reading: unbracketed right side '2 max_{X⊔Y∈S} r(X) + c(Y) − (R + C)/2' → 2(r(X) + c(Y)) − R − C for each stable X ⊔ Y, i.e. 2(max (r(X) + c(Y)) − (R + C)/2); reason: the proof ends with '≥ 2r(X) + 2c(Y) − R − C'; the other parse is weaker
--   - encoding: max over the stable family S → ∀ stable X ⊔ Y; reason: S is finite and nonempty (∅ ⊔ ∅), so the two forms are equivalent
--   - reading: §2 standing assumptions (p.4): A nonnegative with neither zero rows nor zero columns, r and c positive vectors, [n] for a positive integer n → hypotheses hA, hrow, hcol, hr, hc and a nonempty row index type; reason: these are stated once at the top of §2 and apply to every result of the section
--   - encoding: index sets [n] and [m] → finite types ι and κ (ι nonempty); reason: any finite type is in bijection with some [n]; no instance changes
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 2.2, p.5

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **Lemma 2.2.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 2.2, p.5: "For every scaling Ã of A, it holds
∥Ã1 − r∥₁ + ∥Ã⊤1 − c∥₁ ≥ 2 max_{X⊔Y∈S} r(X) + c(Y) − (R + C)/2."

Setting of §2 (p.4): `A` is a nonnegative `n × m` matrix with neither zero rows nor zero columns,
`r`, `c` are positive vectors, `R = r([n])`, `C = c([m])` (`R = C` is **not** assumed, p.5), and a
scaling is `Ã_ij = A_ij x_i y_j` with positive `x`, `y`.

**Formalization Note.** The right side is read as `2 (max_{X⊔Y∈S} (r(X) + c(Y)) − (R + C)/2)`, the
form the proof establishes (it ends with "≥ 2r(X) + 2c(Y) − R − C" for each stable `X ⊔ Y`). The
maximum over the finite, nonempty family `S` of stable sets is encoded by quantifying over every
stable `X ⊔ Y`.

Row and column indices are finite types `ι`, `κ` with `ι` nonempty (the paper's `[n]`, `[m]`
for positive integers `n`, `m`, p.4; `κ` is then nonempty because `A` has no zero row). -/
theorem lemma_2_2 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (x : ι → ℝ) (y : κ → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (X : Finset ι) (Y : Finset κ) (hXY : IsStable A X Y) :
    2 * (∑ i ∈ X, r i) + 2 * (∑ j ∈ Y, c j) - (∑ i, r i) - (∑ j, c j) ≤
      (∑ i, |(∑ j, A i j * x i * y j) - r i|) + (∑ j, |(∑ i, A i j * x i * y j) - c j|) := by sorry

end SinkhornHall
