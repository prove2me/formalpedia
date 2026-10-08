-- Prove2me | Theorems.Thm_RevShareCoord_Single_buyback_realized_equivalence
-- name    : RevShareCoord.Single.buyback_realized_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:41:19.561212+00:00
-- url     : https://prove2.me/theorems/729937f7-3bd3-42a5-8f6e-5994783f3f14
-- title:
--   Sec. 2.3, p. 9 — the buy-back contract {p(1 − φ), p(1 − φ) + φc} and revenue sharing {φ, φc} give the same realized profits
-- statement:
--   Consider the fixed-price newsvendor with retail price $p$, unit production cost $c$, order quantity $q$ and realized demand $D$. Let the supplier offer either the buy-back contract
--
--   $$
--   b^* = p(1-\phi), \qquad w_b^* = p(1-\phi) + \phi c,
--   $$
--
--   or the revenue-sharing contract $\{\phi, \phi c\}$. Then the two contracts give the retailer the same realized profit, and give the supplier the same realized profit:
--
--   $$
--   p\min(q,D) + b^*(q-D)^+ - w_b^* q = \phi\, p\min(q,D) - \phi c\, q,
--   $$
--   $$
--   w_b^* q - b^*(q-D)^+ - cq = (1-\phi)\, p\min(q,D) + \phi c\, q - cq ,
--   $$
--
--   for every order quantity and every realization of demand. In the paper's terms, a buy-back is equivalent to reducing the retailer's unit purchase cost to $w_b - b$ and the share of revenue he keeps to $(p-b)/p$; at $\{b^*, w_b^*\}$ these are $\phi c$ and $\phi$.
--
--   **Formalization Note.** The identities hold for all real $p, c, \phi, q, D$ and are stated without the model's sign restrictions ($p, c > 0$, $\phi \in [0,1]$, $q, D \ge 0$), which they do not need. Expected profits are not formalized; the pathwise identity is the paper's stronger claim and implies equality of expected profits for any demand distribution.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 9 (PDF p. 10), Section 2.3, the paragraph after 'Suppose the supplier offers: b* = p(1 − φ), w*_b = p(1 − φ) + φc'

import Mathlib
import Definitions.Def_RevShareCoord_Single_Newsvendor

namespace RevShareCoord.Single

/-- Sec. 2.3, p. 9: with `b* = p(1 − φ)` and `w_b* = p(1 − φ) + φc`, the buy-back contract
`{b*, w_b*}` and the revenue-sharing contract `{φ, φc}` give the retailer the same realized profit,
and the supplier the same realized profit, for every order quantity `q` and every realization `D`
of demand. -/
theorem buyback_realized_equivalence (p c φ q D : ℝ) :
    bbRetailerRealized p (p * (1 - φ)) (p * (1 - φ) + φ * c) q D =
        rsRetailerRealized p φ (φ * c) q D ∧
      bbSupplierRealized (p * (1 - φ)) (p * (1 - φ) + φ * c) c q D =
        rsSupplierRealized p φ (φ * c) c q D := by sorry

end RevShareCoord.Single
