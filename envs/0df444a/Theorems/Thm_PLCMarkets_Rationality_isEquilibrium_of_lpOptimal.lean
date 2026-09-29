-- Prove2me | Theorems.Thm_PLCMarkets_Rationality_isEquilibrium_of_lpOptimal
-- name    : PLCMarkets.Rationality.isEquilibrium_of_lpOptimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:00:57.561373+00:00
-- url     : https://prove2.me/theorems/7ea562d5-e219-43aa-8de3-b782c641e67f
-- title:
--   §4 — any optimal solution of the LP with positive prices gives equilibrium prices
-- statement:
--   Let $M$ be a Fisher market with additively separable piecewise-linear concave utilities, and let $p'$ be equilibrium prices with $p'_j>0$ for every good and $\sum_jp'_j=\sum_ie(i)$. Let $(p,f)$ be an optimal solution of the linear program of Section 4 built from $p'$ (see `RationalityLP`) whose prices are all positive, $p_j>0$. Then
--   $$p\ \text{ are equilibrium prices of } M.$$
--
--   This is the step of the proof of Theorem 4.1 that turns an optimal vertex of a rational LP into rational equilibrium prices.
--
--   **Formalization Note.** The paper claims this for any optimal solution. Positivity of the solution's prices is added: at a zero price the bang-per-buck constraints no longer order the buyers' segments, and Section 3, on which the argument rests, is stated only for nonzero prices. Positivity of $p'$ and $\sum_jp'_j=\sum_ie(i)$ are the standing assumptions of Section 3 under which the LP is defined.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, https://doi.org/10.1145/1970392.1970394, p. 10:8, §4, second paragraph ("any optimal solution to this LP will be equilibrium prices")

import Mathlib
import Definitions.Def_PLCMarkets_Rationality_RationalityLP

namespace PLCMarkets.Rationality

/-- **§4, second paragraph** (Vazirani–Yannakakis 2011, p. 10:8): any optimal solution of the LP
constructed from the equilibrium prices `p'` gives equilibrium prices. The prices `p'` are
positive and sum to the total money (the standing assumptions of Section 3 under which the LP's
data are defined); the optimal solution's prices are
assumed positive, which the page leaves implicit. -/
theorem isEquilibrium_of_lpOptimal {n g : ℕ} (M : FisherMarket n g) (p' : Fin g → ℝ)
    (hp' : M.IsEquilibrium p')
    (hpos : ∀ j, 0 < p' j)
    (hsum : ∑ j, p' j = ∑ i, (M.budget i : ℝ))
    (z : FisherMarket.LPPoint n g) (hz : M.IsLPOptimal p' z)
    (hzpos : ∀ j, 0 < z.p j) :
    M.IsEquilibrium z.p := by sorry

end PLCMarkets.Rationality
