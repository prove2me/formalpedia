-- Prove2me | Theorems.Thm_VaccineAMC_Framework_joint_surplus_7
-- name    : VaccineAMC.Framework.joint_surplus_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:09.470295+00:00
-- url     : https://prove2.me/theorems/faf73528-570e-4602-87a0-b02952ba253d
-- title:
--   Equation (7) — framework AMC joint surplus
-- statement:
--   Under the standing model conditions and Assumption 1, for a temporary subsidy at full capacity output $Q$, with duration $T$ determined by the fund accounting identity, the discounted gains from trade are
--
--   $$\frac1r\left[\alpha B(Q)-cQ+sQ(1-e^{-rT})\right].$$
--
--   This is the sum of donor benefit, production cost, and committed subsidy over the AMC and tail periods. It supplies the continuation surplus split by Nash bargaining. **Formalization Note** The equality is stated on the branch $sQ>rF$ where $T$ is finite.
-- source:
--   Kremer, Levin & Snyder, Designing Advance Market Commitments for New Vaccines, BFI Working Paper No. 2020-175 (Dec. 2020), p. 12 (PDF 15), equation (7)

import Mathlib
import Definitions.Def_VaccineAMC_Framework_Model

namespace VaccineAMC.Framework

theorem joint_surplus_7 (θ : Params) (hS : θ.Standing) (hA1 : Assumption1 θ) (s F Q : ℝ)
    (hs : 0 < s) (hF : 0 < F) (hTemp : θ.r * F < s * Q) :
    jointTS θ s F Q Q = 1 / θ.r *
      (θ.α * θ.B Q - θ.c * Q +
        s * Q * (1 - Real.exp (-(θ.r * amcLength θ s F Q)))) := by sorry

end VaccineAMC.Framework
