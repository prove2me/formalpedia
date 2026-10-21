-- Prove2me | Theorems.Thm_PolyClinch_TwoSided_corollary_3_10
-- name    : PolyClinch.TwoSided.corollary_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:52.367981+00:00
-- url     : https://prove2.me/theorems/98aa4dfb-3722-4909-bf8a-8971a84620ec
-- title:
--   Corollary 3.10, p. 13 — Mechanism 2 satisfies (ICb) and (IRb)
-- statement:
--   Let $\mathcal I$ be valid public information, $\varepsilon>0$, let $v\in(\varepsilon\mathbb N)^N$ be the buyers' true valuations, and let $i$ be a buyer. If $\mathcal A$ is an output of Mechanism 2 on $\mathcal I$ and $\mathcal A'$ an output on $\mathcal I_i$ (bid of $i$ replaced by $v_i$), then, with the utility (2) computed with the true valuation $v_i$ and budget $B_i$,
--   $$
--   u_i(\mathcal A)\le u_i(\mathcal A'),\qquad u_i(\mathcal A')\ge0 .
--   $$
--   Truthful bidding is a dominant strategy for each buyer in Mechanism 2, and it gives nonnegative utility.
--
--   **Formalization Note** Outputs are any allocations in the relation `Mech2Outcome` (any run of Algorithm 2 on either input). True valuations are on the $\varepsilon$-grid (Assumption 3.2), since the mechanism is run on $\mathcal I_i$.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, p. 13, Corollary 3.10

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Clinching

namespace PolyClinch.TwoSided

/-- Corollary 3.10 (Hirai–Sato p. 13). Mechanism 2 satisfies (ICb) and (IRb): for a valid input
`I`, true valuations `val` on the `ε`-grid and a buyer `i`, every output `A` on `I` and every
output `A'` on `I_i` (bid of `i` replaced by `val i`) satisfy `u_i(A) ≤ u_i(A')` and
`u_i(A') ≥ 0`. -/
theorem corollary_3_10 {n m : ℕ} (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε)
    (I : PublicInfo E) (hI : Valid E ε I) (val : Fin n → ℝ) (hval : ∀ i, OnGrid ε (val i))
    (i : Fin n) (A A' : Allocation E) (hA : Mech2Outcome E I ε A)
    (hA' : Mech2Outcome E (withBid E I i (val i)) ε A') :
    buyerUtility E I val A i ≤ buyerUtility E I val A' i ∧
      0 ≤ buyerUtility E I val A' i := by sorry

end PolyClinch.TwoSided
