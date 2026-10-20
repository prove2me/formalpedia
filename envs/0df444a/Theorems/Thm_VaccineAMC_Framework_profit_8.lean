-- Prove2me | Theorems.Thm_VaccineAMC_Framework_profit_8
-- name    : VaccineAMC.Framework.profit_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:16.318814+00:00
-- url     : https://prove2.me/theorems/687816b1-ab04-49bf-9203-070e7412a62d
-- title:
--   Equation (8) — firm profit under a temporary subsidy
-- statement:
--   Suppose $Q<D(c)$ and $sQ>rF$. With full capacity utilization in both periods, the firm's ex ante value under a framework AMC is
--
--   $$\frac{\beta}{r}\left[\alpha B(Q)-cQ+sQ(1-e^{-rT})\right]-KQ=\pi(Q,\theta)+\beta F.$$
--
--   The second identity isolates the contribution of the escrow fund to the firm's value on the temporary branch. **Formalization Note** The value on the left is defined from the supremum of bargained joint surplus over feasible outputs, before this identity is asserted.
-- source:
--   Kremer, Levin & Snyder, Designing Advance Market Commitments for New Vaccines, BFI Working Paper No. 2020-175 (Dec. 2020), p. 13 (PDF 16), equation (8)

import Mathlib
import Definitions.Def_VaccineAMC_Framework_Model

namespace VaccineAMC.Framework

theorem profit_8 (θ : Params) (hS : θ.Standing) (hA1 : Assumption1 θ)
    (s F Q : ℝ) (hs : 0 < s) (hF : 0 < F)
    (hQ : Q < demand θ θ.c) (hTemp : θ.r * F < s * Q) :
    firmValueTS θ s F Q = θ.β / θ.r *
      (θ.α * θ.B Q - θ.c * Q +
        s * Q * (1 - Real.exp (-(θ.r * amcLength θ s F Q)))) - θ.K * Q ∧
    firmValueTS θ s F Q = profitNA θ Q + θ.β * F := by sorry

end VaccineAMC.Framework
