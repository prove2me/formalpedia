-- Prove2me | Theorems.Thm_SellingData_ListsRotation_reduced_rent_form
-- name    : SellingData.ListsRotation.reduced_rent_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:34.750964+00:00
-- url     : https://prove2.me/theorems/4cf93739-4238-4d27-811f-cd70ac648889
-- title:
--   Proof of Proposition 5, p. 32 — (14) integrated by parts with rent $R(\alpha_H)$; the $\alpha_L$ part is the benchmark, so $\alpha^*_L=\alpha^e_L$ in (14)
-- statement:
--   In the rotation-order model:
--
--   1. for $\alpha_H,\alpha_L\in(0,1)$, integrating by parts turns the objective of (14) into
--   $$\theta\Big[\int_{c_H}^{\bar v}[1-H(v,\alpha_H)]\,dv-k(\alpha_H)\Big]+(1-\theta)\Big[\int_{c_L}^{\bar v}[1-H(v,\alpha_L)]\,dv-\int_{c_L}^{c_H}[1-H(v,\alpha_H)]\,dv-k(\alpha_L)\Big],$$
--   where $R(\alpha_H)=\int_{c_L}^{c_H}[1-H(v,\alpha_H)]\,dv$ is the high type's rent;
--   2. the problem separates: $(\alpha_H,\alpha_L)$ maximizes (14) over $[\underline\alpha,\bar\alpha]^2$ if and only if $\alpha_H$ maximizes
--   $$\theta\Big[\int_{c_H}^{\bar v}(v-c_H)\,dH(v,\alpha_H)-k(\alpha_H)\Big]-(1-\theta)\,R(\alpha_H)$$
--   over $[\underline\alpha,\bar\alpha]$ and $\alpha_L$ maximizes the benchmark objective $(1-\theta)\big[\int_{c_L}^{\bar v}(v-c_L)\,dH(v,\alpha_L)-k(\alpha_L)\big]$, i.e. $\alpha_L$ is efficient for $c_L$.
--
--   Part 2 is the statement $\alpha^*_L=\alpha^e_L$ for the reduced problem: the low-cost marketers' informativeness is chosen exactly as under the observable-cost benchmark. No range condition on the costs is needed.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 32, proof of Proposition 5, first paragraph

import Mathlib
import Definitions.Def_SellingData_ListsRotation_Setting

namespace SellingData.ListsRotation

/-- Proof of Proposition 5, p. 32: (i) integrating by parts, (14) equals
`θ [∫_{c_H}^{v̄} [1 - H(v, α_H)] dv - k(α_H)] + (1 - θ) [∫_{c_L}^{v̄} [1 - H(v, α_L)] dv
 - ∫_{c_L}^{c_H} [1 - H(v, α_H)] dv - k(α_L)]`, with rent `R(α_H) = ∫_{c_L}^{c_H} [1 - H(v, α_H)] dv`;
(ii) the problem separates: `(α_H, α_L)` maximizes (14) iff `α_H` maximizes
`θ [∫_{c_H}^{v̄} (v - c_H) dH(v, α_H) - k(α_H)] - (1 - θ) R(α_H)` and `α_L` is efficient for
`c_L`, so `α*_L = α^e_L` in (14). -/
theorem reduced_rent_form (M : Model) :
    (∀ αH ∈ Set.Ioo (0 : ℝ) 1, ∀ αL ∈ Set.Ioo (0 : ℝ) 1,
      M.reducedProfit αH αL =
        M.θ * ((∫ v in M.cH..M.vHi, (1 - M.H v αH)) - M.k αH) +
          (1 - M.θ) * ((∫ v in M.cL..M.vHi, (1 - M.H v αL)) -
            (∫ v in M.cL..M.cH, (1 - M.H v αH)) - M.k αL)) ∧
    (∀ αH αL : ℝ, M.IsReducedMax αH αL ↔
      ((αH ∈ Set.Icc M.aLo M.aHi ∧ ∀ β ∈ Set.Icc M.aLo M.aHi,
          M.benchProfit M.θ β M.cH - (1 - M.θ) * M.rent β ≤
            M.benchProfit M.θ αH M.cH - (1 - M.θ) * M.rent αH) ∧
        M.IsEfficient (1 - M.θ) M.cL αL)) := by sorry

end SellingData.ListsRotation
