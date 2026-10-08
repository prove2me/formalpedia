-- Prove2me | Theorems.Thm_RetailVariety_Fashion_eq_12
-- name    : RetailVariety.Fashion.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:52.370976+00:00
-- url     : https://prove2.me/theorems/91fc19d3-26ce-4e9d-96b3-6d403167922e
-- title:
--   (12) — $\sum_{j\le r}g(v_j)\le\sum_{j\le r}g(w'_j)$, and the same for $g^T$
-- statement:
--   Under the model hypotheses ($0<c<p$, $\lambda>0$, $\sigma>0$, $0\le\beta<1$, $v_0>0$), let $v,w\in\mathbb R^n$ be nonnegative, sorted decreasingly, with $v\prec w$; let $r\le n$, $1\le t\le r$ and $0<\delta\le 1$ with $\sum_{j=1}^{t-1}w_j+\delta w_t=\sum_{j=1}^{r}v_j$; let $w'$ be as in the proof of Theorem 3 and $L=\sum_{j=1}^r v_j+v_0$. Then
--   $$\sum_{j=1}^{r}g(v_j)\le\sum_{j=1}^{r}g(w'_j)\tag{12}$$
--   and
--   $$\sum_{j=1}^{r}g^{T}(v_j)\le\sum_{j=1}^{r}g^{T}(w'_j).$$
--
--   The left-hand side is the optimal profit of the more fashionable category; the right-hand side is the profit of a fractional assortment of the less fashionable one.
--
--   **Formalization Note.** Lean's `t` is the paper's $t-1$ and `θ` the paper's $\delta$; $L$ is passed with the defining equation `hL`. The paper restricts to $0<\beta<1$ when defining $g$; (12) is stated for $0\le\beta<1$.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1506, (12) and the trend-following paragraph of the proof of Theorem 3

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Majorization
import Definitions.Def_RetailVariety_Fashion_ProofObjects

namespace RetailVariety.Fashion

/-- (12), p. 1506: `∑_{j=1}^r g(v_j) ≤ ∑_{j=1}^r g(w′_j)`, and the same with `g^T`, where
`L = ∑_{j=1}^r v_j + v_0`. Lean's `t` is the paper's `t − 1` and `θ` the paper's `δ`. -/
theorem eq_12 {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (hvw : Majorized v w) (r : ℕ) (hr : r ≤ n)
    (t : ℕ) (ht : t < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (heq : ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩ = ∑ j ∈ RetailVariety.Statics.A n r, v j)
    (L : ℝ) (hL : L = ∑ j ∈ RetailVariety.Statics.A n r, v j + v0) :
    ∑ j : Fin r, gFun p c lam σ β L (v (Fin.castLE hr j)) ≤
        ∑ j : Fin r, gFun p c lam σ β L (wPrime w r t θ hr j) ∧
      ∑ j : Fin r, gFunT p c lam L (v (Fin.castLE hr j)) ≤
        ∑ j : Fin r, gFunT p c lam L (wPrime w r t θ hr j) := by sorry

end RetailVariety.Fashion
