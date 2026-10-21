-- Prove2me | Theorems.Thm_VWAPContract_Optimal_proposition_5_full_insurance
-- name    : VWAPContract.Optimal.proposition_5_full_insurance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:04.270092+00:00
-- url     : https://prove2.me/theorems/531268ea-7c94-4e61-b19a-5c15471ead22
-- title:
--   Proof of Proposition 5, p. 53 (PDF 54) — $\tau^{VWAP}(p,v(x^{FB}(\eta),\eta))-p\cdot x^{FB}(\eta)=0$
-- statement:
--   Under the guaranteed VWAP contract, the first-best schedule makes the dealer's realized payment equal the realized trading cost:
--
--   $$\tau^{\mathrm{VWAP}}(p,v(x^{\mathrm{FB}}(\eta),\eta))-p\cdot x^{\mathrm{FB}}(\eta)=0.$$
--
--   This is condition (ii) of Lemma 4. It holds pointwise for every market and shock realization in the model, so the dealer's payoff is fully insured at the recommended policy.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), p. 53 (PDF 54), proof of Proposition 5, last paragraph

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem proposition_5_full_insurance {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (hM : M.Standing) :
    ∀ ω, pay M tauVWAP xFB ω = cost M xFB ω := by sorry

end VWAPContract.Optimal
