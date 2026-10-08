-- Prove2me | Theorems.Thm_RetailVariety_Fashion_wPrime_majorized
-- name    : RetailVariety.Fashion.wPrime_majorized
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:25.17941+00:00
-- url     : https://prove2.me/theorems/69e8d816-6eff-4d1d-bc3b-5f3218a282f6
-- title:
--   Proof of Theorem 3 — $\sum w'_j=\sum_{j\le r}v_j$ and $(v_1,\dots,v_r)\prec w'$
-- statement:
--   Let $v,w\in\mathbb R^n$ be nonnegative and sorted decreasingly with $v\prec w$, let $r\le n$, and let $1\le t\le r$ and $0<\delta\le 1$ satisfy $\sum_{j=1}^{t-1}w_j+\delta w_t=\sum_{j=1}^{r}v_j$. Let $w'=(w_1,\dots,w_{t-1},\delta w_t,0,\dots,0)\in\mathbb R^r$. Then
--   $$\sum_{j=1}^{r}w'_j=\sum_{j=1}^{r}v_j\qquad\text{and}\qquad (v_1,\dots,v_r)\prec w'.$$
--
--   The $r$ most popular variants of the more fashionable category are majorized by a truncated, partially scaled copy of the less fashionable one, which puts the comparison in a form where Lemma 2 applies in dimension $r$.
--
--   **Formalization Note.** Lean's `t` is the paper's $t-1$ and `θ` the paper's $\delta$; both vectors live on `Fin r`, embedded in `Fin n` by `Fin.castLE`.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1506, proof of Theorem 3

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Majorization
import Definitions.Def_RetailVariety_Fashion_ProofObjects

namespace RetailVariety.Fashion

/-- p. 1506: with `t, δ` as chosen above, `∑_{j=1}^r w′_j = ∑_{j=1}^r v_j` and
`(v_1, …, v_r) ≺ w′` in `ℝ^r`. Lean's `t` is the paper's `t − 1` and `θ` the paper's `δ`. -/
theorem wPrime_majorized {n : ℕ} (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (hvw : Majorized v w) (r : ℕ) (hr : r ≤ n)
    (t : ℕ) (ht : t < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (heq : ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩ = ∑ j ∈ RetailVariety.Statics.A n r, v j) :
    ∑ j : Fin r, wPrime w r t θ hr j = ∑ j : Fin r, v (Fin.castLE hr j) ∧
      Majorized (fun j : Fin r => v (Fin.castLE hr j)) (wPrime w r t θ hr) := by sorry

end RetailVariety.Fashion
