-- Prove2me | Theorems.Thm_VaccineAMC_Framework_accounting_6
-- name    : VaccineAMC.Framework.accounting_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:16.488752+00:00
-- url     : https://prove2.me/theorems/85470ba4-2bda-4179-ba1d-bbd7b5044ae2
-- title:
--   Equation (6) and (A9) — fund exhaustion time
-- statement:
--   Under the standing model conditions and Assumption 1, let $s,F>0$ and suppose $sq^A>rF$. The unique positive duration $T$ at which the escrow fund is exhausted is
--
--   $$T=\frac1r\log\frac{sq^A}{sq^A-rF},\qquad F=\int_0^T sq^A e^{-rt}\,dt=\frac{sq^A}{r}(1-e^{-rT}).$$
--
--   The identity connects the fund's stock $F$ to its discounted subsidy flow, with interest accruing in escrow. **Formalization Note** The Lean integral uses the open interval $(0,T)$; endpoint choices have the same integral.
-- source:
--   Kremer, Levin & Snyder, Designing Advance Market Commitments for New Vaccines, BFI Working Paper No. 2020-175 (Dec. 2020), p. 12 (PDF 15), equation (6); p. 37 (PDF 40), equation (A9)

import Mathlib
import Definitions.Def_VaccineAMC_Framework_Model

namespace VaccineAMC.Framework

theorem accounting_6 (θ : Params) (hS : θ.Standing) (hA1 : Assumption1 θ) (s F : ℝ)
    (hs : 0 < s) (hF : 0 < F) (qA : ℝ) (hTemp : θ.r * F < s * qA) :
    let T := amcLength θ s F qA
    0 < T ∧
    (∫ t in Set.Ioo 0 T, s * qA * Real.exp (-(θ.r * t))) = F ∧
    F = s * qA / θ.r * (1 - Real.exp (-(θ.r * T))) ∧
    (∀ T' : ℝ, 0 < T' →
      (∫ t in Set.Ioo 0 T', s * qA * Real.exp (-(θ.r * t))) = F → T' = T) := by sorry

end VaccineAMC.Framework
