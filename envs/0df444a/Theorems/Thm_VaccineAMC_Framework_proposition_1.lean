-- Prove2me | Theorems.Thm_VaccineAMC_Framework_proposition_1
-- name    : VaccineAMC.Framework.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:18.007976+00:00
-- url     : https://prove2.me/theorems/c6f09bbc-8c38-40b8-8fb4-94218498607e
-- title:
--   Proposition 1 — integrated capacity and output
-- statement:
--   Under the standing assumptions and Assumption 1, the unique integrated optimum has capacity and output
--
--   $$Q^{\mathrm{IN}}=q^{\mathrm{IN}}=D(c+\kappa)>0.$$
--
--   The integrated benchmark prices both current production and the annuitized capacity investment at their full costs. It is the comparison point for the hold-up loss in Proposition 2.
-- source:
--   Kremer, Levin & Snyder, Designing Advance Market Commitments for New Vaccines, BFI Working Paper No. 2020-175 (Dec. 2020), p. 10 (PDF 13), Proposition 1

import Mathlib
import Definitions.Def_VaccineAMC_Framework_Model

namespace VaccineAMC.Framework

theorem proposition_1 (θ : Params) (hS : θ.Standing) (hA1 : Assumption1 θ) :
    (∀ Q q : ℝ, IsIntegratedOpt θ Q q ↔
      Q = demand θ (θ.c + θ.κ) ∧ q = Q) ∧
    0 < demand θ (θ.c + θ.κ) := by sorry

end VaccineAMC.Framework
