-- Prove2me | Theorems.Thm_TradeCreditIns_Cancelable_pi2_first_best
-- name    : TradeCreditIns.Cancelable.pi2_first_best
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:40.798763+00:00
-- url     : https://prove2.me/theorems/ab9f7f8b-7107-4a62-abf4-8e978a380721
-- title:
--   Proof of Proposition 3, steps 1 and 3 — the contract attains the first-best
-- statement:
--   Under the attractive-outside-option and efficient-monitoring regime of Proposition 3, the supplier's payoff from the proposed contract is
--
--   $$
--   \Pi_2=\theta_1(1-\beta_1)r+(\theta_2+\theta_3)r_0-c,
--   $$
--
--   and $\Pi_2=\Pi^{FB}$, the centralized first-best payoff. This is the paper's “full value” assertion in numerical form.
--
--   **Formalization Note** Signal 1 is index 0. The contract and decisions use the strict tie choices of (64)–(66), and the first-best remains a maximum over policies rather than a definition by this expression.
-- source:
--   Yang, Bakshi & Chen, Trade credit insurance: operational value and contract choice, accepted manuscript (Management Science 67(2), 2021; LBS Research Online eprint 1343), proof of Proposition 3, steps 1 and 3, pp. xi–xii (PDF 43–44), equations (60)–(67)

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model

namespace TradeCreditIns.Cancelable

/-- Proof of Proposition 3, steps 1 and 3, pp. xi–xii (PDF 43–44). -/
theorem pi2_first_best (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) :
    supplierPayoff P (κstar P) =
        P.θ 0 * (1 - P.β 0) * P.r +
          (P.θ 1 + P.θ 2) * P.r0 - P.c ∧
    P.θ 0 * (1 - P.β 0) * P.r +
          (P.θ 1 + P.θ 2) * P.r0 - P.c = firstBest P := by sorry

end TradeCreditIns.Cancelable
