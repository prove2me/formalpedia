-- Prove2me | Theorems.Thm_SampleRemoval_lemma_3_2
-- name    : SampleRemoval.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:13:16.530841+00:00
-- url     : https://prove2.me/theorems/75f3042d-d5a1-44b3-92d6-a0231de2e1a0
-- title:
--   Lemma 3.2 — sparse optimal weights
-- statement:
--   Assume the design is in general position, and let $\mathcal W$ be the feasible set of a pair $(e,\theta)$. Let $w\in\mathcal W$ with $\|w\|_1>d-1$. Then there is $w'\in\mathcal W$ with
--
--   $$
--   \|w'\|_1\ge\|w\|_1,\qquad \beta(w')=\beta(w),\qquad \#\{i:\ 0<w'_i<1\}\le d .
--   $$
--
--   Any feasible weighting of mass above $d-1$ can thus be replaced by one that is at least as heavy, has the same fit, and is fractional in at most $d$ coordinates. It is the first step of the rounding in Theorem 3.3.
--
--   Differences from the source:
--
--   - encoding: observations (x_i, y_i) ∈ ℝᵈ × ℝ indexed by i ∈ [n] → x : Fin n → Fin d → ℝ, y : Fin n → ℝ, paper index i = Lean index i − 1; reason: Lean convention; same instances
--   - encoding: ∥w∥₁ → ∑ i, w i; reason: every weight lies in [0, 1], so the sum of the coordinates is the ℓ¹ norm
--   - generalization: (e, θ) is a target, ⟨e, β([n])⟩ > θ (§2, Audits) → (e, θ) ∈ ℝᵈ × ℝ arbitrary; reason: the statement and its proof do not use the target condition; taking a target specializes to the source's claim
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Lemma 3.2, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_SampleRemoval_ols
import Definitions.Def_SampleRemoval_feasible
import Definitions.Def_SampleRemoval_GeneralPosition

set_option autoImplicit false

namespace SampleRemoval

/-- **Lemma 3.2 (Sparse optimal weights)** (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), p.4). Assume GP. Let `w ∈ 𝒲` with
`∥w∥₁ > d − 1`. Then there is `w′ ∈ 𝒲` with `∥w′∥₁ ≥ ∥w∥₁`, `β(w′) = β(w)`, and at most `d`
coordinates of `w′` in `(0, 1)`.

**Formalization Note** `∥w∥₁` is `∑ i, w i` (weights lie in `[0, 1]`). `𝒲` is `feasible x y e θ`
for an arbitrary pair `(e, θ)`; the paper's `(e, θ)` is a target (`⟨e, β([n])⟩ > θ`), which the
statement does not need and does not assume. -/
theorem lemma_3_2 {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ) (θ : ℝ)
    (hGP : GeneralPosition x) (w : Fin n → ℝ) (hw : w ∈ feasible x y e θ)
    (hmass : (d : ℝ) - 1 < ∑ i, w i) :
    ∃ w' ∈ feasible x y e θ, ∑ i, w i ≤ ∑ i, w' i ∧ ols x y w' = ols x y w ∧
      (Finset.univ.filter (fun i => 0 < w' i ∧ w' i < 1)).card ≤ d := by sorry

end SampleRemoval
