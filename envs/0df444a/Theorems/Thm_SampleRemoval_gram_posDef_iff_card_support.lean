-- Prove2me | Theorems.Thm_SampleRemoval_gram_posDef_iff_card_support
-- name    : SampleRemoval.gram_posDef_iff_card_support
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:08:22.286835+00:00
-- url     : https://prove2.me/theorems/0e0021a3-e1a9-41af-b7b2-1313361194cc
-- title:
--   §2 — under GP, $G(w)\succ0$ iff $|\mathrm{supp}(w)|\ge d$
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$ be in general position (every $d$ of them are linearly independent), and let $w\in[0,1]^n$. Then
--
--   $$
--   G(w)=\sum_i w_ix_ix_i^{\top}\succ0\iff |\mathrm{supp}(w)|\ge d,\qquad \mathrm{supp}(w)=\{i: w_i\neq0\}.
--   $$
--
--   Under general position, whether a weighting has a well-defined least-squares fit depends only on how many observations it keeps. The paper uses this fact in the proofs of Lemma 3.2 and Theorem 3.3 to certify that the Gram matrices of sparse and rounded weightings are nonsingular.
--
--   Differences from the source:
--
--   - encoding: observations (x_i, y_i) ∈ ℝᵈ × ℝ indexed by i ∈ [n] → x : Fin n → Fin d → ℝ, y : Fin n → ℝ, paper index i = Lean index i − 1; reason: Lean convention; same instances
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), §2, General position, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_SampleRemoval_gram
import Definitions.Def_SampleRemoval_GeneralPosition

set_option autoImplicit false

open Matrix

namespace SampleRemoval

/-- **§2, General position** (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), p.3): "Under GP, G(w) ≻ 0 if and only if |supp(w)| ≥ d."

If the design is in general position, then for every weight vector `w ∈ [0, 1]ⁿ` the Gram matrix
`G(w) = Σᵢ wᵢ xᵢ xᵢ⊤` is positive definite if and only if `w` has at least `d` nonzero
coordinates.

**Formalization Note** The domain `w ∈ [0, 1]ⁿ` is the paragraph's ("For a weight vector
w ∈ [0, 1]n", same page); with negative weights the equivalence fails. `supp(w)` is
`{i : wᵢ ≠ 0}`. Both directions are stated. -/
theorem gram_posDef_iff_card_support {n d : ℕ} (x : Fin n → Fin d → ℝ)
    (hGP : GeneralPosition x) (w : Fin n → ℝ) (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) :
    (gram x w).PosDef ↔ d ≤ (Finset.univ.filter (fun i => w i ≠ 0)).card := by sorry

end SampleRemoval
