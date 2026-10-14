-- Prove2me | Theorems.Thm_SellingData_AppendsRotation_eq15_integrated_efficient_high
-- name    : SellingData.AppendsRotation.eq15_integrated_efficient_high
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:40.078255+00:00
-- url     : https://prove2.me/theorems/e065d0d1-8fc6-4347-a42c-511ea27c877a
-- title:
--   Proof of Proposition 7, p. 33 — (15) integrated by parts; its maximizers have α_H = α^e_H
-- statement:
--   In the data-append model, for all $\alpha_H,\alpha_L\in(0,1)$ the objective (15) equals
--   $$
--   \Pi(\alpha_H,\alpha_L)=\theta\Big[\int_{c_H}^{\bar v}[1-H(v,\alpha_H)]\,dv-\int_{c_H}^{c_L}[1-H(v,\alpha_L)]\,dv-k(\alpha_H)\Big]+(1-\theta)\Big[\int_{c_L}^{\bar v}[1-H(v,\alpha_L)]\,dv-k(\alpha_L)\Big]-\hat u+c_L ,
--   $$
--   where $\int_{c_H}^{c_L}=-\int_{c_L}^{c_H}$ (oriented integral, as printed).
--
--   Moreover, $(\alpha_H,\alpha_L)$ maximizes $\Pi$ over $[\underline\alpha,\bar\alpha]^2$ if and only if
--
--   1. $\alpha_H$ is efficient for the high-cost type, i.e. maximizes the benchmark $\theta\big[\int_{c_H}^{\bar v}(v-c_H)\,dH(v,\alpha)-k(\alpha)\big]$ over $[\underline\alpha,\bar\alpha]$; and
--   2. $\alpha_L\in[\underline\alpha,\bar\alpha]$ maximizes $-\theta\big[P(\alpha,c_H)-P(\alpha,c_L)\big]+(1-\theta)\big[P(\alpha,c_L)-k(\alpha)\big]$ over $[\underline\alpha,\bar\alpha]$, where $P(\alpha,c)=\int_c^{\bar v}(v-c)\,dH(v,\alpha)$.
--
--   In particular the reduced problem supplies the high-cost type efficiently, $\alpha^*_H=\alpha^e_H$, for every $c_L<c_H$, with no condition on the position of the rotation point.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 33, proof of Proposition 7

import Mathlib
import Definitions.Def_SellingData_AppendsRotation_Setting

namespace SellingData.AppendsRotation

open Set

/-- Proof of Proposition 7, p. 33. Integrating (15) by parts gives
`Π = θ[∫_{c_H}^{v̄}[1 − H(v, α_H)]dv − ∫_{c_H}^{c_L}[1 − H(v, α_L)]dv − k(α_H)]
  + (1 − θ)[∫_{c_L}^{v̄}[1 − H(v, α_L)]dv − k(α_L)] − û + c_L`,
and `(α_H, α_L)` maximizes (15) over `[α̲, ᾱ]²` exactly when `α_H` is efficient for the high-cost
type (`α*_H = α^e_H`) and `α_L` maximizes the `α_L`-part of (15). -/
theorem eq15_integrated_efficient_high (M : Model) :
    (∀ αH ∈ Ioo (0 : ℝ) 1, ∀ αL ∈ Ioo (0 : ℝ) 1,
      M.reducedProfit αH αL =
        M.θ * ((∫ v in M.cH..M.vHi, (1 - M.H v αH)) - (∫ v in M.cH..M.cL, (1 - M.H v αL)) - M.k αH) +
          (1 - M.θ) * ((∫ v in M.cL..M.vHi, (1 - M.H v αL)) - M.k αL) - M.uHat + M.cL) ∧
    (∀ αH αL : ℝ, M.IsReducedOptimal αH αL ↔
      (M.IsEfficient M.θ M.cH αH ∧ αL ∈ Icc M.aLo M.aHi ∧
        ∀ b ∈ Icc M.aLo M.aHi,
          -M.θ * (M.payoff b M.cH - M.payoff b M.cL) + (1 - M.θ) * (M.payoff b M.cL - M.k b) ≤
            -M.θ * (M.payoff αL M.cH - M.payoff αL M.cL) +
              (1 - M.θ) * (M.payoff αL M.cL - M.k αL))) := by sorry

end SellingData.AppendsRotation
