-- Prove2me | Theorems.Thm_RefugeeCash_PDCA_clipped_branches
-- name    : RefugeeCash.PDCA.clipped_branches
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:31.25279+00:00
-- url     : https://prove2.me/theorems/356810ae-b17e-47ac-807d-1d68630dc18d
-- title:
--   §6.3, p. 22 (PDF 23) — where k(p) = 0 the retailer earns π_0(p) ≤ Π_0; where k(p) = 1 it earns B(1 − c/p) + π_0(p)
-- statement:
--   In the symmetric-goods model with $B > 0$, $c > 0$ and Assumption 2 (with maximizer $p_0$ and $\Pi_0 = \pi_0(p_0)$), let $k(p)$ be the PDCA scheme (27) for any target $(p^\odot,k^\odot)$, and let $p > c$ be a retail price.
--   1. If the scheme pays no cash at $p$, $k(p) = 0$, then the retailer's profit reduces to its pre-refugee-arrival profit and is at most the pre-arrival maximum:
--   $$k(p)B\Big(1-\frac cp\Big) + \pi_0(p) = \pi_0(p) \le \Pi_0 .$$
--   2. If the scheme pays the whole budget in cash at $p$, $k(p) = 1$, then
--   $$k(p)B\Big(1-\frac cp\Big) + \pi_0(p) = B\Big(1-\frac cp\Big) + \pi_0(p).$$
--
--   These are the two clipped branches of the PDCA profit, which together with the strictly concave middle branch make the retailer's profit piecewise concave.
--
--   **Formalization Note** The bound $\pi_0(p) \le \Pi_0$ renders the page's "the pre-refugee-arrival level"; it holds because $p_0$ maximizes $\pi_0$ on $(c,\infty)$ under Assumption 2.
-- source:
--   Kotsi, Wu & Pedraza-Martinez, Donations for Refugee Crises: In-kind Versus Cash Assistance, manuscript of November 27, 2021 (MSOM, DOI 10.1287/msom.2021.1073), p. 22 (PDF 23), §6.3, paragraph after eq. (27)

import Mathlib
import Definitions.Def_RefugeeCash_PDCA_Model

namespace RefugeeCash.PDCA

/-- §6.3, p. 22 (PDF 23): at a price `p > c` where the PDCA scheme (27) pays no cash (`k(p) = 0`),
the retailer's profit is `π0(p)`, at most the pre-refugee-arrival level `Π0`; where it pays the
whole budget in cash (`k(p) = 1`), the retailer's profit is `B(1 − c/p) + π0(p)`. -/
theorem clipped_branches (P : Params) (hP : P.Standing) (pmax p0 : ℝ)
    (hA2 : Assumption2 P pmax p0) (pT kT p : ℝ) (hp : P.c < p) :
    (kPDCA P pT kT p = 0 → pdcaProfit P pT kT p = pi0 P p ∧ pdcaProfit P pT kT p ≤ Pi0 P p0) ∧
      (kPDCA P pT kT p = 1 → pdcaProfit P pT kT p = P.B * (1 - P.c / p) + pi0 P p) := by sorry

end RefugeeCash.PDCA
