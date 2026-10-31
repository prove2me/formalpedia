-- Prove2me | Theorems.Thm_StreamSubmod_rounding
-- name    : StreamSubmod.rounding
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:26.907521+00:00
-- url     : https://prove2.me/theorems/24fae12d-2230-4d50-b969-d8d0c4fb53b4
-- title:
--   Rounding: a fractional point of $\ell_1$-norm at most $k$ rounds to a set worth at least $F(x)$
-- statement:
--   Let $f:2^V\to\mathbb R$ be submodular, with multilinear extension $F$, and let $x\in[0,1]^V$ satisfy $\|x\|_1\le k$. Then there is a set $A$ contained in the support of $x$, with $|A|\le k$, such that
--
--   $$
--   f(A)\ge F(x).
--   $$
--
--   The proof of Lemma 6 applies this to the vector $(b\mathbf 1_{\hat S_i})\vee\mathbf 1_{\mathrm{OPT}\setminus O}$, citing Pipage Rounding and Swap Rounding. It turns a fractional solution into a feasible input for the guarantee of OfflineAlg.
--
--   Differences from the source:
--   - generalization: the vector (b1_Ŝi) ∨ 1_{OPT\O}, whose support lies in Ŝi ∪ (OPT \ O) → every x ∈ [0,1]^V with ‖x‖₁ ≤ k, and a set inside the support of x; reason: the page uses only ‖x‖₁ ≤ k and this support property, and the instance is a special case
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, proof of Lemma 6, p.9, "standard rounding techniques such as Pipage Rounding [13] and Swap Rounding [18] can be used"

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Rounding (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, proof of Lemma 6, p.9,
"standard rounding techniques such as Pipage Rounding [13] and Swap Rounding [18] can be used"):
for a submodular `f`, every fractional point `x ∈ [0,1]^E` with `‖x‖₁ ≤ k` can be rounded to a set
`A` inside the support of `x`, with `|A| ≤ k` and `f(A) ≥ F(x)`.

**Formalization Note.** The proof of Lemma 6 applies this to `x = (b𝟏_{Ŝᵢ}) ∨ 𝟏_{OPT\O}`. -/
theorem rounding {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf : Submodular f)
    (k : ℕ) (x : E → ℝ) (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e ≤ 1)
    (hxk : ∑ e, x e ≤ (k : ℝ)) :
    ∃ A : Finset E, (∀ e ∈ A, 0 < x e) ∧ A.card ≤ k ∧ F f x ≤ f A := by sorry

end StreamSubmod
