-- Prove2me | Theorems.Thm_PointRedemption_eq_2
-- name    : PointRedemption.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:26.877766+00:00
-- url     : https://prove2.me/theorems/c451869d-ecb9-4f65-824e-e89f8b539ff2
-- title:
--   Eq. (2), p. 12 — the marginal-value form of the pricing objective $J_t(p,y)$
-- statement:
--   Consider the point-redemption pricing model (parameters $\lambda,q,\bar\beta,R$, laws $F$ of the reservation price and $G$ of the point value, $\beta=1-\bar\beta$). Let $t\ge1$ periods to go and $y\ge1$ units, and write $\Delta=\Delta_{t-1}(y)=V_{t-1}(y)-V_{t-1}(y-1)$ for the marginal value of inventory. Then for every real price $p$ the objective $J_t(p,y)$ of the optimality equations (1) equals
--
--   $$J_t(p,y)=\lambda\bar\beta\Big[\bar F(p)\bar G(p/q)(p-\Delta)+I(p)(R-\Delta)\Big]+\lambda\beta\Big[\bar F(p)(p-\Delta)\Big]+V_{t-1}(y),$$
--
--   where $I(p)=\int_0^{p/q}\bar F(qx)\,dG(x)$ is the point-purchase probability of a reward consumer.
--
--   The identity splits the period's revenue into its three sources (cash sales to reward consumers, reward sales, cash sales to cash-only consumers), each measured against the marginal value of the unit sold. It is the starting point of the first-order analysis of Theorem 1 and Proposition 1.
--
--   **Formalization Note** $J_t$ is defined by the printed formula (1), not by (2).
--
--   Differences from the source:
--   - encoding: β̄(q) at the fixed q; t = 1, …, T periods with horizon T → βbar a number in [0,1] with β = 1 − βbar; t ≥ 1 counts periods to go, no horizon T; reason: the paper fixes q and writes β̄ for β̄(q) (p. 11); T only bounds t, so every t ≥ 1 is an instance of some horizon
--   - reading: R, the reimbursement, with no sign stated → R ≥ 0 (a field of the model); reason: R is revenue from the point issuer; Prop. 5(b) writes "any reimbursement rate R > 0"
-- source:
--   Chung–Ahn–Chun, Dynamic Pricing with Point Redemption, SSRN 3426903 (KAIST WP KCB-WP-2019-013); MSOM (2022), doi:10.1287/msom.2021.1067, eq. (2), p. 12 (PDF 13)

import Mathlib
import Definitions.Def_PointRedemption_Model

namespace PointRedemption

open MeasureTheory ProbabilityTheory

/-- **Eq. (2)**, Chung–Ahn–Chun, *Dynamic Pricing with Point Redemption*, SSRN 3426903; MSOM
(2022), doi:10.1287/msom.2021.1067, p. 12 (PDF 13). With `Δ = Δ_{t−1}(y)`, the objective
`J_t(p, y)` of (1) equals
`λβ̄[F̄(p)Ḡ(p/q)(p − Δ) + I(p)(R − Δ)] + λβ[F̄(p)(p − Δ)] + V_{t−1}(y)`.

**Formalization Note.** `J` is the printed (1), not (2); `β = 1 − β̄`, `F = 1 − F̄`. `t` counts
periods to go. -/
theorem eq_2 (P : Params) (t y : ℕ) (ht : 1 ≤ t) (hy : 1 ≤ y) (p : ℝ) :
    P.J t p y =
      P.lam * P.βbar *
          (P.Fbar p * P.Gbar (p / P.q) * (p - P.Δ (t - 1) y) + P.I p * (P.R - P.Δ (t - 1) y)) +
        P.lam * P.β * (P.Fbar p * (p - P.Δ (t - 1) y)) + P.V (t - 1) y := by sorry

end PointRedemption
