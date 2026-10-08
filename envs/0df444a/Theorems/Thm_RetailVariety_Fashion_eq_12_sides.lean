-- Prove2me | Theorems.Thm_RetailVariety_Fashion_eq_12_sides
-- name    : RetailVariety.Fashion.eq_12_sides
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T20:00:02.448997+00:00
-- url     : https://prove2.me/theorems/7c8612c1-598c-46e1-89f2-24a2462bc34f
-- title:
--   Proof of Theorem 3 — the sides of (12) are $\pi(A_r, v)$ and $h(\delta w_t)$ with $S=A_{t-1}$
-- statement:
--   In the setting of (12), with $L=\sum_{j=1}^r v_j+v_0$:
--   1. $\displaystyle \pi_I(A_r,v)=\sum_{j=1}^{r}g(v_j)$ and $\displaystyle\pi_T(A_r,v)=\sum_{j=1}^{r}g^{T}(v_j)$;
--   2. if $\beta>0$, $\displaystyle\sum_{j=1}^{r}g(w'_j)=h_I(\delta w_t)$, where $h_I$ is the Lemma 1 function of category $w$ (no-purchase preference $w_0=v_0$) with $S=A_{t-1}$;
--   3. $\displaystyle\sum_{j=1}^{r}g^{T}(w'_j)=h_T(\delta w_t)$, with $h_T$ the Lemma 1 function of category $w$ with $S=A_{t-1}$.
--
--   Together with (12), Lemma 1 and the end-point identities, these give $\pi(A_r,v)\le\max\{\pi(A_{t-1},w),\pi(A_t,w)\}$.
--
--   **Formalization Note.** Lean's `t` is the paper's $t-1$, so `A n t` is the paper's $A_{t-1}$ and `w ⟨t, _⟩` is $w_t$; `θ` is the paper's $\delta$. Part 2 needs $\beta>0$ because $g(0)=0$ fails at $\beta=0$ ($0^0=1$). Only the hypotheses the identities use are kept (in particular, majorization is not assumed here).
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1506, proof of Theorem 3

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Lemma1Functions
import Definitions.Def_RetailVariety_Fashion_ProofObjects

namespace RetailVariety.Fashion

/-- p. 1506: the left side of (12) is `π(A_r, v)`, and (for `0 < β` in the independent model) the
right side is `h(δ w_t)`, the Lemma 1 function of category `w` with `S = A_{t−1}`. Lean's `t` is the
paper's `t − 1` (so `A n t` is the paper's `A_{t−1}`) and `θ` the paper's `δ`. -/
theorem eq_12_sides {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j) (r : ℕ) (hr : r ≤ n)
    (t : ℕ) (ht : t < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (heq : ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩ = ∑ j ∈ RetailVariety.Statics.A n r, v j)
    (L : ℝ) (hL : L = ∑ j ∈ RetailVariety.Statics.A n r, v j + v0) :
    profitI p c lam σ β v v0 (RetailVariety.Statics.A n r) = ∑ j : Fin r, gFun p c lam σ β L (v (Fin.castLE hr j)) ∧
      profitT p c lam v v0 (RetailVariety.Statics.A n r) = ∑ j : Fin r, gFunT p c lam L (v (Fin.castLE hr j)) ∧
      (0 < β → ∑ j : Fin r, gFun p c lam σ β L (wPrime w r t θ hr j) =
        hI p c lam σ β w v0 (RetailVariety.Statics.A n t) (θ * w ⟨t, by omega⟩)) ∧
      ∑ j : Fin r, gFunT p c lam L (wPrime w r t θ hr j) =
        hT p c lam w v0 (RetailVariety.Statics.A n t) (θ * w ⟨t, by omega⟩) := by sorry

end RetailVariety.Fashion
