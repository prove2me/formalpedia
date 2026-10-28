-- Prove2me | Theorems.Thm_SolarTariff_Fair_proposition_5b_cs
-- name    : SolarTariff.Fair.proposition_5b_cs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:29.676915+00:00
-- url     : https://prove2.me/theorems/ec4503dc-9a2f-4b0e-b579-7bdd3fc31a5d
-- title:
--   Proposition 5(b), p. 18 — T* is free of cross-subsidization
-- statement:
--   In a market satisfying the standing assumptions, let the target outcome $A$ be nonempty and admissible. If the customers' aggregate financial gain is nonnegative, then tariff $T^*$ leaves no tier with a positive increase in per-household cash outflow:
--
--   $$\Delta_C\ge0\quad\Longrightarrow\quad \max_i\Delta\mathrm{outflow}_i(T^*,t(m))\le0.$$
--
--   By Definition 1, the induced outcome is free of cross-subsidization. This is the first sentence of Proposition 5(b).
--
--   **Formalization Note** A nonempty tier type is explicit because the paper's maximum is over $I\ge1$ tiers. The target has at least one adopter and satisfies $\Delta_E^A\le E^0$.
-- source:
--   Singh & Scheller-Wolf, That’s Not Fair: Tariff Structures for Electric Utilities with Rooftop Solar, SSRN 2926676 (SSRN Version), p. 18 (PDF 18), Proposition 5(b), first sentence; p. S.3 (PDF 35), proof

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

namespace SolarTariff.Fair

theorem proposition_5b_cs {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Market ι) (hM : M.Standing) (A : Finset ι)
    (hA : Admissible M A) (hC : 0 ≤ dC M A) :
    objective M ((TStar M A).bills M) A (tm M A) ≤ 0 := by sorry

end SolarTariff.Fair
