-- Prove2me | Theorems.Thm_ResolvingNRM_FRUpper_lp_rhs_sensitivity
-- name    : ResolvingNRM.FRUpper.lp_rhs_sensitivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:43:41.312095+00:00
-- url     : https://prove2.me/theorems/fd4a284c-ef1f-40b9-a9d2-7570c3321f71
-- title:
--   Eq. (33) — the DLP value changes by at most Σ_l r^l_max (b_l − b'_l)⁺ when the capacity right-hand side drops
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$ have nonnegative entries $a_{lj}$, let $r \ge 0$ and $\lambda_j > 0$, and for $b \ge 0$ let
--   $$v(b) = \max\Big\{ \sum_{j=1}^n r_j x_j \ :\ \sum_{j=1}^n A_j x_j \le b,\ 0 \le x_j \le \lambda_j \Big\}.$$
--   With $r^l_{\max} = \max_{j \in [n]} \{ r_j \, \mathbb{I}(a_{lj} > 0)/a_{lj} \}$, for all capacity vectors $b, b' \ge 0$,
--   $$v(b) - v(b') \le \sum_{l=1}^m r^l_{\max} \, (b_l - b'_l)^+ .$$
--
--   Applied with $b = C/T$ and $b' = b(t)$, the average remaining capacity of the FR policy in period $t$, this is eq. (33) of the paper: it converts the per-period gap between the DLP and the LP that FR solves into the positive parts $(b_l - b_l(t))^+$, which Lemma 8 controls. The number $r^l_{\max}$ bounds the dual price of resource $l$.
--
--   **Formalization Note.** The paper states (33) for the two LPs it compares ($b$ and $b(t)$); the statement here is for arbitrary right-hand sides $b, b' \ge 0$, as the paper's justification ("only differ in the right hand side") is. The printed sum runs over $l = 1, \dots, L$; the paper has $m$ resources, so it is read as $l \in [m]$. $\lambda_j > 0$, $r \ge 0$ and $a_{lj} \ge 0$ are the model's standing assumptions (p. 7). With $b, b' \ge 0$ the LP is feasible and bounded, so `piValue` is its maximum.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, App. C.2, eq. (33), p. 35

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_FRUpper_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.FRUpper

/-- Eq. (33), App. C.2, p. 35: two DLPs (2) that differ only in the capacity right-hand side
satisfy `v(b) − v(b') ≤ ∑_l r^l_max (b_l − b'_l)⁺`. -/
theorem lp_rhs_sensitivity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (b b' : Fin m → ℝ) (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    piValue A r b lam - piValue A r b' lam ≤ ∑ l, rmaxRes A r l * max (b l - b' l) 0 := by sorry

end ResolvingNRM.FRUpper
