-- Prove2me | Theorems.Thm_RefMNLPricing_Myopic_revenue_monotone
-- name    : RefMNLPricing.Myopic.revenue_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:06.475928+00:00
-- url     : https://prove2.me/theorems/10497f6f-ab44-49d2-a2c7-610377959f80
-- title:
--   §3.1, p. 13 — the optimal single-period revenue Π^m(r) is monotone increasing in the reference price r
-- statement:
--   Consider the MNL pricing model with reference effects, with $b_i>0$, $c_i^\pm\ge0$, price box $\mathcal P^n=[0,p_H]^n$, $p_H>0$, and the ceiling assumption $p_H\ge\hat p_H$. For a reference price $r\in\mathcal P^n$ let $\Pi^m(r) = \max_{p\in\mathcal P^n}\Pi(p,r)$ be the optimal single-period revenue. Then $\Pi^m$ is monotone increasing in $r$ with respect to the coordinatewise order:
--
--   $$
--   r,\,r'\in\mathcal P^n,\quad r \le r' \ \text{coordinatewise} \quad\Longrightarrow\quad \Pi^m(r)\le\Pi^m(r').
--   $$
--
--   A higher reference price yields a larger optimal single-period revenue. This monotonicity is one of the ingredients of the long-run analysis of the myopic price path.
--
--   **Formalization Note** $\Pi^m(r)$ and $\Pi^m(r')$ are represented as the revenues $\Pi(p,r)$, $\Pi(p',r')$ of arbitrary maximisers $p$ at $r$ and $p'$ at $r'$ over the box. "Monotone increasing" is read non-strictly. The statement is the unlabelled sentence after Theorem 2 on p. 13, under the standing assumptions of §3.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), §3.1, p. 13, paragraph after Theorem 2; standing assumption §2.4, p. 11

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model

namespace RefMNLPricing.Myopic

/-- §3.1, p. 13, paragraph after Theorem 2: the optimal single-period revenue `Π^m(r)` is monotone
increasing in the reference price `r` (coordinatewise order on `Pⁿ`). Stated for arbitrary
maximisers `p` at `r` and `p'` at `r'`, whose revenues are `Π^m(r)` and `Π^m(r')`. -/
theorem revenue_monotone {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (hpH : 0 < pH)
    (hceil : CeilingOK a b cp cm pH)
    (r r' p p' : Fin n → ℝ) (hr : InBox pH r) (hr' : InBox pH r') (hle : r ≤ r')
    (hp : IsBoxMax a b cp cm pH r p) (hp' : IsBoxMax a b cp cm pH r' p') :
    revenue a b cp cm p r ≤ revenue a b cp cm p' r' := by sorry

end RefMNLPricing.Myopic
