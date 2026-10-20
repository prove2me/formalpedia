-- Prove2me | Theorems.Thm_VaccineAMC_Framework_full_capacity
-- name    : VaccineAMC.Framework.full_capacity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:22.234972+00:00
-- url     : https://prove2.me/theorems/d968eb2b-9cbb-4495-8e2f-0c0e28e2044e
-- title:
--   Proof of Proposition 3 — full capacity utilization
-- statement:
--   Suppose $Q<D(c)$ and the fund would be exhausted at full AMC-period output, $sQ>rF$. Under the standing assumptions, Assumption 1, and positive $s,F$, the Nash-efficient continuation bargain selects full output in both periods:
--
--   $$q^A=q^T=Q.$$
--
--   This is the capacity-utilization principle invoked in the framework AMC calculation. **Formalization Note** The temporary-branch condition is explicit: if the subsidy is perpetual even at full output, the tail never occurs and its output is not determined.
-- source:
--   Kremer, Levin & Snyder, Designing Advance Market Commitments for New Vaccines, BFI Working Paper No. 2020-175 (Dec. 2020), proof of Proposition 3, p. 38 (PDF 41); tail-period observation §3.4, p. 12 (PDF 15)

import Mathlib
import Definitions.Def_VaccineAMC_Framework_Model

namespace VaccineAMC.Framework

theorem full_capacity (θ : Params) (hS : θ.Standing) (hA1 : Assumption1 θ)
    (s F Q : ℝ) (hs : 0 < s) (hF : 0 < F)
    (hQ : Q < demand θ θ.c) (hTemp : θ.r * F < s * Q) :
    ∀ qA qT : ℝ, IsBargainTS θ s F Q qA qT ↔ qA = Q ∧ qT = Q := by sorry

end VaccineAMC.Framework
