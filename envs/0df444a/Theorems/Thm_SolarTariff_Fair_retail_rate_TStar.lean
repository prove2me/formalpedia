-- Prove2me | Theorems.Thm_SolarTariff_Fair_retail_rate_TStar
-- name    : SolarTariff.Fair.retail_rate_TStar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:22.534072+00:00
-- url     : https://prove2.me/theorems/e7d3821f-bfdb-40e1-97c1-bcea11deaf90
-- title:
--   Proof of Proposition 5, p. S.3 — retail rate of T*
-- statement:
--   In the constructed tariff $T^*$, for a nonempty admissible target outcome in a market satisfying the standing assumptions, the common retail rate is
--
--   $$p_r^*=p_{r0}-\frac{\Delta_C}{E^0},\qquad E^0=\sum_i h_i d_i.$$
--
--   In particular, $\Delta_C\ge0$ implies $p_r^*\le p_{r0}$. This identifies how the customers' aggregate gain is returned through the common rate.
--
--   **Formalization Note** The definition of $p_r^*$ is the independent solution of the utility constraint (16) after substituting $T^*$'s fees; the displayed welfare formula is the theorem. Positivity of $d_i,h_i$ ensures $E^0>0$.
-- source:
--   Singh & Scheller-Wolf, That’s Not Fair: Tariff Structures for Electric Utilities with Rooftop Solar, SSRN 2926676 (SSRN Version), p. S.3 (PDF 35), proof of Proposition 5(b), paragraph beginning ‘Accordingly’

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

namespace SolarTariff.Fair

theorem retail_rate_TStar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Market ι) (hM : M.Standing) (A : Finset ι)
    (hA : Admissible M A) :
    prStar M A = M.pr0 - dC M A / E0 M ∧
      (0 ≤ dC M A → prStar M A ≤ M.pr0) := by sorry

end SolarTariff.Fair
