-- Prove2me | Theorems.Thm_PointRedemption_eq_7
-- name    : PointRedemption.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:39.514575+00:00
-- url     : https://prove2.me/theorems/3448fe5c-fe8f-4eec-a5fb-ec19253146e9
-- title:
--   Eq. (7), App. p. 1 — the derivative of $J_t(\cdot,y)$ and its factored form
-- statement:
--   In the point-redemption pricing model, let $t\ge1$, $y\ge1$, $\Delta=\Delta_{t-1}(y)$, and let $p>0$ be a price at which the density $f$ is continuous and the density $g$ is continuous at $p/q$. Then $p\mapsto J_t(p,y)$ is differentiable at $p$ with derivative
--
--   $$\frac{\partial J_t(p,y)}{\partial p}=\lambda\bar\beta\Big[\Big(-f(p)\bar G(p/q)-\bar F(p)\frac{g(p/q)}{q}\Big)(p-\Delta)+\bar F(p)\bar G(p/q)+\bar F(p)\frac{g(p/q)}{q}(R-\Delta)\Big]+\lambda\beta\Big[-f(p)(p-\Delta)+\bar F(p)\Big].$$
--
--   If moreover $\bar F(p)>0$ and $1-\bar\beta G(p/q)>0$, this derivative equals
--
--   $$\lambda\big(1-\bar\beta G(p/q)\big)\bar F(p)\left[1-\frac{f(p)}{\bar F(p)}(p-\Delta)-\frac{\bar\beta g(p/q)/q}{1-\bar\beta G(p/q)}(p-R)\right].$$
--
--   The factored form shows that the sign of the derivative is the sign of the bracket, which compares the hazard rate of the reservation price with the hazard of the point-purchase channel; it is the first-order condition used for Theorem 1 and Proposition 1.
--
--   **Formalization Note** The paper writes "$=0$" after (7) because it is the first-order condition at the optimum; this item states the derivative identity itself.
--
--   Differences from the source:
--   - reading: (7): ∂J_t/∂p = … = 0, the first-order condition → HasDerivAt (J_t(·, y)) D p with D the first line of (7), and D equal to the second line; reason: the "= 0" holds only at the optimum; the identity of the two lines with the derivative is what the proof uses
--   - generalization: differentiable densities (f′, g′ in (8)) → f continuous at p and g continuous at p/q, at the price p only; reason: continuity at the point is all the fundamental theorem of calculus needs; differentiable densities are continuous
--   - encoding: division by F̄(p) and 1 − β̄G(p/q) in the second line → the second line is asserted when F̄(p) > 0 and 1 − β̄G(p/q) > 0; reason: nondegeneracy that only excludes the cases where the printed quotient is undefined
--   - encoding: (7) at the prices p ≥ 0 over which (1) maximizes → p > 0; reason: at p = 0 the integral I(p) has its lower endpoint and J_t(·, y) is in general only right-differentiable; the two-sided derivative of (7) is meant at interior prices
--   - encoding: β̄(q) at the fixed q; t = 1, …, T periods with horizon T → βbar a number in [0,1] with β = 1 − βbar; t ≥ 1 counts periods to go, no horizon T; reason: the paper fixes q and writes β̄ for β̄(q) (p. 11); T only bounds t, so every t ≥ 1 is an instance of some horizon
--   - reading: R, the reimbursement, with no sign stated → R ≥ 0 (a field of the model); reason: R is revenue from the point issuer; Prop. 5(b) writes "any reimbursement rate R > 0"
-- source:
--   Chung–Ahn–Chun, Dynamic Pricing with Point Redemption, SSRN 3426903 (KAIST WP KCB-WP-2019-013); MSOM (2022), doi:10.1287/msom.2021.1067, Appendix A, proof of Theorem 1, eq. (7), App. p. 1 (PDF 36)

import Mathlib
import Definitions.Def_PointRedemption_Model

namespace PointRedemption

open MeasureTheory ProbabilityTheory

/-- **Eq. (7)** (proof of Theorem 1), Chung–Ahn–Chun, *Dynamic Pricing with Point Redemption*,
SSRN 3426903; MSOM (2022), doi:10.1287/msom.2021.1067, Appendix A, App. p. 1 (PDF 36).
For `t ≥ 1`, `y ≥ 1` and a price `p > 0` at which `f` is continuous and `g` is continuous at
`p/q`, write `Δ = Δ_{t−1}(y)`. Then `J_t(·, y)` has at `p` the derivative
`λβ̄[(−f(p)Ḡ(p/q) − F̄(p)g(p/q)/q)(p − Δ) + F̄(p)Ḡ(p/q) + F̄(p)g(p/q)/q·(R − Δ)]`
`+ λβ[−f(p)(p − Δ) + F̄(p)]`,
and, when `F̄(p) > 0` and `1 − β̄G(p/q) > 0`, this derivative equals
`λ(1 − β̄G(p/q))F̄(p)[1 − (f(p)/F̄(p))(p − Δ) − ((β̄g(p/q)/q)/(1 − β̄G(p/q)))(p − R)]`.

**Formalization Note.** The "= 0" of (7) is the first-order condition at the optimum; this item
states the derivative identity the proof uses. Continuity of `f` at `p` and of `g` at `p/q` is all
the fundamental theorem of calculus needs (the paper assumes differentiable densities). -/
theorem eq_7 (P : Params) (t y : ℕ) (ht : 1 ≤ t) (hy : 1 ≤ y) (p : ℝ) (hp : 0 < p)
    (hf : ContinuousAt P.f p) (hg : ContinuousAt P.g (p / P.q)) :
    HasDerivAt (fun x => P.J t x y)
        (P.lam * P.βbar *
            ((-P.f p * P.Gbar (p / P.q) - P.Fbar p * P.g (p / P.q) / P.q) * (p - P.Δ (t - 1) y) +
              P.Fbar p * P.Gbar (p / P.q) +
              P.Fbar p * P.g (p / P.q) / P.q * (P.R - P.Δ (t - 1) y)) +
          P.lam * P.β * (-P.f p * (p - P.Δ (t - 1) y) + P.Fbar p)) p ∧
      (0 < P.Fbar p → 0 < 1 - P.βbar * P.G (p / P.q) →
        P.lam * P.βbar *
            ((-P.f p * P.Gbar (p / P.q) - P.Fbar p * P.g (p / P.q) / P.q) * (p - P.Δ (t - 1) y) +
              P.Fbar p * P.Gbar (p / P.q) +
              P.Fbar p * P.g (p / P.q) / P.q * (P.R - P.Δ (t - 1) y)) +
          P.lam * P.β * (-P.f p * (p - P.Δ (t - 1) y) + P.Fbar p) =
        P.lam * (1 - P.βbar * P.G (p / P.q)) * P.Fbar p *
          (1 - P.f p / P.Fbar p * (p - P.Δ (t - 1) y) -
            (P.βbar * P.g (p / P.q) / P.q) / (1 - P.βbar * P.G (p / P.q)) * (p - P.R))) := by sorry

end PointRedemption
