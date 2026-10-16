-- Prove2me | Theorems.Thm_PELiquidity_Primary_eq18
-- name    : PELiquidity.Primary.eq18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:56.14499+00:00
-- url     : https://prove2.me/theorems/79a15889-3abc-468b-beec-1e7ca8d9cf22
-- title:
--   (18), p. 24 — the indifference rate R̄^max_PE,H lies in (1 + r(λ, δ_L), pR) and equalizes H- and L-fund profits
-- statement:
--   Fix the model parameters. Let $\bar f^*_H=\dfrac{p^2B}{p^2-q^2}$ be the expected fee of an $H$-fund, $\bar f^*_L=\dfrac{pB}{p-q}\hat x(\lambda,\delta_L)$ that of an $L$-fund (Proposition 1), and $\bar R_L=1+r(\lambda,\delta_L)$. Define
--   $$\bar R^{max}_{PE,H}=\frac{\bar f^*_L\,(pR-\bar f^*_H)}{\dfrac{\bar f^*_H}{1+r(\lambda,\delta_L)}(pR-\bar f^*_L)+\bar f^*_L-\bar f^*_H}.\qquad(18)$$
--   Then $1+r(\lambda,\delta_L)<\bar R^{max}_{PE,H}<pR$, and with the fund size $I(\bar R,\bar f)=\bar R A/(\bar R-(pR-\bar f))$ given by (3),
--   $$\bar f^*_H\,I\big(\bar R^{max}_{PE,H},\bar f^*_H\big)=\bar f^*_L\,I\big(1+r(\lambda,\delta_L),\bar f^*_L\big).$$
--
--   That is, $\bar R^{max}_{PE,H}$ is the highest return a GP is willing to pay for $H$-LPs' capital: at this rate an $H$-fund is exactly as profitable as an $L$-fund paying $L$-LPs their break-even return. It exceeds $L$-LPs' return, which is the source of the return premium of Proposition 2 i).
--
--   **Formalization Note** The printed denominator has $f^*_L-f^*_H$ without bars; these are the same expected fees $\bar f^*_L,\bar f^*_H$.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 24, (18); p. 47, Appendix C.3, (C.2)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Primary

/-- (18): with `f̄_H = p²B/(p² - q²)`, `f̄_L = pB x̂(λ, δ_L)/(p - q)` and
`R̄_L = 1 + r(λ, δ_L)`, the rate `R̄^max_PE,H` of (18) lies strictly between `R̄_L` and
`pR` and equalizes the GP profits `f̄ I` of an H-fund at `R̄^max_PE,H` and an L-fund at
`R̄_L`, where `I = R̄ A / (R̄ - (pR - f̄))` is the fund size from (3). -/
theorem eq18 (P : Params) :
    let fH := P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2)
    let fL := P.p * P.B * xHat P.lam P.δL / (P.p - P.q)
    let RL := grossReturn P.lam P.δL
    let Rmax := fL * (P.p * P.R - fH) / (fH / RL * (P.p * P.R - fL) + fL - fH)
    RL < Rmax ∧ Rmax < P.p * P.R ∧
      fH * (Rmax * P.A / (Rmax - (P.p * P.R - fH))) =
        fL * (RL * P.A / (RL - (P.p * P.R - fL))) := by sorry

end PELiquidity.Primary
