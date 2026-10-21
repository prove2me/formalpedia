-- Prove2me | Theorems.Thm_SolarTariff_Fair_proposition_5
-- name    : SolarTariff.Fair.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:26.685214+00:00
-- url     : https://prove2.me/theorems/a195c881-9a0e-4191-9583-e8d178dc8540
-- title:
--   Proposition 5, p. 18 — T* is feasible, CS-free when customers gain, and optimal within T3 when the smallest-demand tier does not adopt
-- statement:
--   Fix a finite market satisfying the model's standing assumptions and a nonempty target adopting set $A$ with $\Delta_E^A\le E^0$. Construct $T^*$ from that target. Proposition 5 asserts three conclusions:
--
--   1. At price $t(m)$, $T^*$ induces exactly $A$; the solar company earns $\Delta_S$ and strictly less at every other real price; and the utility's profit change is $\Delta_U$.
--   2. If $\Delta_C\ge0$, the maximum increase in any tier's customer cash outflow is at most zero, so the outcome is free of cross-subsidization.
--   3. If $\Delta_C\ge0$ and some tier with the smallest demand $d_i$ does not adopt, $T^*$ minimizes that maximum cash-outflow increase among all feasible tariffs of type $T_3$, allowing each competitor its own solar price.
--
--   The result gives a tiered tariff that implements the desired adoption outcome while meeting the solar firm's and utility's profit targets, with the stated equity and optimality guarantees.
--
--   **Formalization Note** The standing predicate makes explicit $h_i,d_i,g_i>0$ so the paper's denominators are nonzero. The paper's threshold ordering is replaced by the induced equilibrium, including the unique solar-company best response; ties favor adoption. The optimality comparison ranges over $T_3$ tariffs as in §4.3, and a minimal-demand nonadopting tier may be any one of several tied minima. The printed slips in (16), (17), (19), and the p. 12 customer-gain formula are resolved using the paper's surrounding derivation and proof.
-- source:
--   Singh & Scheller-Wolf, That’s Not Fair: Tariff Structures for Electric Utilities with Rooftop Solar, SSRN 2926676 (SSRN Version), p. 18 (PDF 18), Proposition 5; p. S.3 (PDF 35), proof

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

namespace SolarTariff.Fair

theorem proposition_5 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Market ι) (hM : M.Standing) (A : Finset ι)
    (hA : Admissible M A) :
    let B := (TStar M A).bills M
    FeasibleP2 M A B (tm M A) ∧
    (0 ≤ dC M A → objective M B A (tm M A) ≤ 0) ∧
    (0 ≤ dC M A → (∃ k, k ∉ A ∧ ∀ i, M.d k ≤ M.d i) →
      ∀ (τ : T3 ι) (ps : ℝ), FeasibleP2 M A (τ.bills M) ps →
        objective M B A (tm M A) ≤ objective M (τ.bills M) A ps) := by sorry

end SolarTariff.Fair
