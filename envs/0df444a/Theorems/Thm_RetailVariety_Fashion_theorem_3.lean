-- Prove2me | Theorems.Thm_RetailVariety_Fashion_theorem_3
-- name    : RetailVariety.Fashion.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:27.540985+00:00
-- url     : https://prove2.me/theorems/344fb53d-e20c-4ce4-8de0-4a62d2094016
-- title:
--   Theorem 3 — if $v\prec w$, the optimal profit of $v$ is at most that of $w$, for $\pi_I$ and $\pi_T$
-- statement:
--   Consider two merchandise categories with the same number $n$ of variants, preference vectors $v,w\in\mathbb R^n$ with nonnegative entries sorted decreasingly ($v_1\ge\cdots\ge v_n\ge0$, $w_1\ge\cdots\ge w_n\ge 0$), the same price and cost $0<c<p$, the same demand volume $\lambda>0$, the same model constants $\sigma>0$, $0\le\beta<1$, and equal no-purchase preferences $v_0=w_0>0$. Let $r,l\in\{0,\dots,n\}$ be such that the prefix sets $A_r$ and $A_l$ are optimal:
--   $$\pi(A_r,v)=\max_{S\subseteq N}\pi(S,v),\qquad \pi(A_l,w)=\max_{S\subseteq N}\pi(S,w).$$
--   If $v\prec w$, that is, $v$ is more fashionable than $w$, then
--   $$\pi(A_r,v)\le\pi(A_l,w).$$
--   This holds both for the independent population profit $\pi=\pi_I$ of (7) and for the trend-following profit $\pi=\pi_T$ of (8).
--
--   The theorem makes precise that fragmentation of preferences is costly: with all else equal, the optimal profit of a more fashionable category is no larger than that of a more basic one.
--
--   **Formalization Note.** The two models are combined in one statement as a conjunction. Optimality of $A_r$ and $A_l$ is stated as hypotheses $\pi(S,\cdot)\le\pi(A_\cdot,\cdot)$ for every $S$, which is how the theorem defines $r$ and $l$; their existence is Theorem 1 of the paper and is not used. $r,l$ range over $\{0,\dots,n\}$ with $A_0=\emptyset$, since in the independent model the empty assortment can be optimal. The range $0\le\beta<1$ is the model's (§2.3.1); the printed proof writes $0<\beta<1$.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, pp. 1505–1506, Theorem 3

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Majorization

namespace RetailVariety.Fashion

/-- Theorem 3 (van Ryzin & Mahajan 1999, pp. 1505–1506). Two categories `v`, `w` with the same
`n` variants (sorted decreasingly, nonnegative preferences), the same `p, c, λ, σ, β` and equal
no-purchase preference `v_0 = w_0`. If `A_r` maximizes `π(·, v)`, `A_l` maximizes `π(·, w)` and
`v ≺ w`, then `π(A_r, v) ≤ π(A_l, w)`, for `π = π_I` (7) and for `π = π_T` (8). -/
theorem theorem_3 {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (r l : ℕ) (hr : r ≤ n) (hl : l ≤ n)
    (hvw : Majorized v w) :
    ((∀ S : Finset (Fin n), profitI p c lam σ β v v0 S ≤ profitI p c lam σ β v v0 (RetailVariety.Statics.A n r)) →
      (∀ S : Finset (Fin n), profitI p c lam σ β w v0 S ≤ profitI p c lam σ β w v0 (RetailVariety.Statics.A n l)) →
      profitI p c lam σ β v v0 (RetailVariety.Statics.A n r) ≤ profitI p c lam σ β w v0 (RetailVariety.Statics.A n l)) ∧
    ((∀ S : Finset (Fin n), profitT p c lam v v0 S ≤ profitT p c lam v v0 (RetailVariety.Statics.A n r)) →
      (∀ S : Finset (Fin n), profitT p c lam w v0 S ≤ profitT p c lam w v0 (RetailVariety.Statics.A n l)) →
      profitT p c lam v v0 (RetailVariety.Statics.A n r) ≤ profitT p c lam w v0 (RetailVariety.Statics.A n l)) := by sorry

end RetailVariety.Fashion
