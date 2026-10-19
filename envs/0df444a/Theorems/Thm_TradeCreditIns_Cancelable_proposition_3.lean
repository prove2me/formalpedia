-- Prove2me | Theorems.Thm_TradeCreditIns_Cancelable_proposition_3
-- name    : TradeCreditIns.Cancelable.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:51.475604+00:00
-- url     : https://prove2.me/theorems/cc6f4a36-651d-485e-82ee-4f0e790e1b3e
-- title:
--   Proposition 3 — the cancelable contract recovers the full value of trade credit insurance
-- statement:
--   Suppose $r_0\ge(1-\beta_2)r$ and $c\le\phi$ under the paper's standing assumptions and Assumptions 1–2. The cancelable contract
--
--   $$
--   \delta=0,\qquad p=f=\frac{c}{\theta_1}+\beta_1r
--   $$
--
--   induces monitoring. The insurer cancels at exactly signals 2 and 3, the supplier ships at exactly signal 1, and her expected payoff equals the planner's first-best payoff $\Pi^{FB}$. Moreover, among all admissible cancelable contracts, none gives the supplier a higher expected payoff.
--
--   This is Proposition 3's optimality and full-value conclusion for an attractive outside option.
--
--   **Formalization Note** Signal 1 is Lean index 0. Admissibility requires a valid contract, insurer monitoring with participation, and actual cancelation at some signal. The comparison ranges over every such contract. The definitions follow the strict tie choices in the proposition's proof, (64)–(66); the standing assumptions disclose $c>0$, $l\ge0$, and $\theta_1>0$.
-- source:
--   Yang, Bakshi & Chen, Trade credit insurance: operational value and contract choice, accepted manuscript (Management Science 67(2), 2021; LBS Research Online eprint 1343), p. 18 (PDF 19), Proposition 3, equation (9)

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model

namespace TradeCreditIns.Cancelable

/-- Proposition 3, p. 18 (PDF 19). -/
theorem proposition_3 (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) :
    Admissible P (κstar P) ∧
    (∀ i, Cancels P (κstar P) (P.β i) ↔ i ≠ 0) ∧
    (∀ i, Ships P (κstar P) (P.β i) ↔ i = 0) ∧
    supplierPayoff P (κstar P) = firstBest P ∧
    ∀ κ, Admissible P κ →
      supplierPayoff P κ ≤ supplierPayoff P (κstar P) := by sorry

end TradeCreditIns.Cancelable
