-- Prove2me | Theorems.Thm_RefugeeCash_PDCA_refugee_profit
-- name    : RefugeeCash.PDCA.refugee_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:59.308577+00:00
-- url     : https://prove2.me/theorems/a291e87b-dcef-431b-a852-1b9a70c00a27
-- title:
--   §5, p. 16 (PDF 17) — refugees spending kB at price p cost the retailer kBc/p, and π_r(p,k) = kB(1 − c/p)
-- statement:
--   In the symmetric-goods model, refugees with cash assistance $kB$ spend it in full at the retail price $p$, buying $Q(p,k) = kB/p$ units. For every price $p \neq 0$ and every $k$, these purchases cost the retailer
--   $$c\,Q(p,k) = \frac{kBc}{p},$$
--   and the retailer's profit from selling to the refugees is
--   $$\pi_r(p,k) = (p-c)\,Q(p,k) = kB\Big(1 - \frac{c}{p}\Big).$$
--
--   This identity turns the retailer's post-arrival profit into equation (18), $\Pi(p,k) = kB(1-c/p) + (p-c)D(p)$, the objective every later statement of the mission works with.
-- source:
--   Kotsi, Wu & Pedraza-Martinez, Donations for Refugee Crises: In-kind Versus Cash Assistance, manuscript of November 27, 2021 (MSOM, DOI 10.1287/msom.2021.1073), p. 16 (PDF 17), §5

import Mathlib
import Definitions.Def_RefugeeCash_PDCA_Model

namespace RefugeeCash.PDCA

/-- §5, p. 16 (PDF 17): with cash assistance `kB` the refugees buy `Q(p, k) = kB/p` units, which
cost the retailer `kBc/p`, and the retailer's profit from the refugees is `πr(p, k) = kB(1 − c/p)`. -/
theorem refugee_profit (P : Params) (p k : ℝ) (hp : p ≠ 0) :
    P.c * refugeeDemand P p k = k * P.B * P.c / p ∧
      piR P p k = k * P.B * (1 - P.c / p) := by sorry

end RefugeeCash.PDCA
