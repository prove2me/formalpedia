-- Prove2me | Theorems.Thm_TimeLockedSales_Reform_proposition_2
-- name    : TimeLockedSales.Reform.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:42.756311+00:00
-- url     : https://prove2.me/theorems/8e767844-dbb1-45d8-ab1e-a1e9d525f5a8
-- title:
--   Proposition 2, p. 13 — sufficiency of recommendation policies
-- statement:
--   In the focus region $v^*\le v_0<v^{**}$, every finite-message information policy has a three-message recommendation policy that customers obey on every realized signal–message pair. For each customer, the replacement policy preserves the ex ante probability of purchase; consequently it preserves the platform's expected revenue:
--   $$\Pr_{\sigma}(a_t=1)=\Pr_{\sigma'}(a_t=1)\quad(1\le t\le T),\qquad R(\sigma)=R(\sigma').$$
--   This is the dynamic reduction from arbitrary messages to recommendations.
--
--   **Formalization Note.** The message types are finite. Obedience is a property of the new policy under the Bayesian purchase rule (2); it is not stipulated as customer behavior. At the printed weak-IC endpoints, obedience can fail, so the theorem uses actual response on positive-probability signal–message pairs. The Lean history index $t$ refers to customer $t+1$.
-- source:
--   Küçükgül, Özer & Wang, Engineering social learning: information design of time-locked sales campaigns for online platforms, submission manuscript (Nov. 2019; published Management Science 2022, doi:10.1287/mnsc.2021.4151), p. 13, Proposition 2; proof pp. 38–40, (B.6)–(B.14)

import Mathlib
import Definitions.Def_TimeLockedSales_Reform_Model

namespace TimeLockedSales.Reform

/-- Proposition 2, p. 13: three obedient recommendations preserve all purchase rates and revenue. -/
theorem proposition_2 (P : Params) (hS : P.Standing) (hR : P.Region)
    {M : Type} [Fintype M] (σ' : InfoPolicy M) :
    ∃ σ : InfoPolicy SignType,
      IsObedient P σ ∧
      (∀ t < P.T, purchaseProb P σ t = purchaseProb P σ' t) ∧
      revenue P σ = revenue P σ' := by sorry

end TimeLockedSales.Reform
