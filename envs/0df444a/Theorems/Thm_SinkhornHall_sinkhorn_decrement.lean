-- Prove2me | Theorems.Thm_SinkhornHall_sinkhorn_decrement
-- name    : SinkhornHall.sinkhorn_decrement
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:16.953039+00:00
-- url     : https://prove2.me/theorems/c56719a9-2505-4e9f-9270-32045df13e10
-- title:
--   Proof of Theorem 4.1 — without a perfect matching each Sinkhorn iteration lowers $\log\kappa$ by at least $4/n^2$
-- statement:
--   Let $A$ be a nonnegative $n\times n$ matrix with no zero row or column whose support graph has no perfect matching, take $(r,c)=(\mathbf 1,\mathbf 1)$, and let $\kappa$ be the capacity (2.2), $\kappa(x,y)=\sum_{i,j}A_{ij}x_iy_j\big/\big(\prod_i x_i^{1/n}\prod_j y_j^{1/n}\big)$. For every positive $x$, with $y=C(x)$, $x'=R(y)$ and $y'=C(x')$,
--
--   $$\log\kappa(x',y')-\log\kappa(x,y)\ \le\ -\frac{4}{n^2}.$$
--
--   This is the per-iteration progress that bounds the number of Sinkhorn iterations in Theorem 4.1.
--
--   Differences from the source:
--   - reading: §4 standing assumptions (p.15): G = G(A) for a nonnegative n × n matrix A, no isolated node, n = |U| = |V|, (r, c) = (1, 1) → A : Matrix (Fin n) (Fin n) ℝ with hA, hrow, hcol, and marginals 1; reason: stated once at the top of §4 and in force for Theorem 4.1 and its proof
--   - reading: 'Suppose that G has no perfect matching' (hypothesis of Theorem 4.1) → hpm : ¬ HasPerfectMatching A; reason: the decrement display is proved under Theorem 4.1's hypothesis
--   - reading: log (base not named) → Real.log (natural logarithm); reason: the constants 1/2 (Pinsker), 4/n² and 1/4 are derived in the natural log
--   - encoding: the chain of inequalities in the display → its endpoints: decrement ≤ −4/n²; reason: the intermediate terms are steps of the proof
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, proof of Theorem 4.1, decrement display, p.16

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **One Sinkhorn iteration lowers `log κ` by at least `4/n²` when there is no perfect matching.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, proof of Theorem 4.1, decrement display, p.16: with
`x′ := R(y)`, `y′ := C(x′)` (p.15) and `y = C(x)`, "log κ(x′, y′) − log κ(x, y) = −D(1∥B1)/n −
D(1∥(B′)⊤1)/n ≤ … ≤ −4/n²", under the hypothesis of Theorem 4.1 that `G` has no perfect matching.

Setting of §4 (p.15): `A` is a nonnegative `n × n` matrix with no zero row or column (no isolated
node of `G = G(A)`), `(r, c) = (1, 1)`, so `R = C = n`.

**Formalization Note.** Rows and columns are `Fin n`; `κ = kappa A 1 1`, `R = rowNorm A 1`,
`C = colNorm A 1`; `log` is `Real.log`. The statement is the endpoint inequality of the chain, for
every positive `x`. -/
theorem sinkhorn_decrement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hpm : ¬ HasPerfectMatching A)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    let y := colNorm A 1 x
    let x' := rowNorm A 1 y
    let y' := colNorm A 1 x'
    Real.log (kappa A 1 1 x' y') - Real.log (kappa A 1 1 x y) ≤ -4 / (n : ℝ) ^ 2 := by sorry

end SinkhornHall
