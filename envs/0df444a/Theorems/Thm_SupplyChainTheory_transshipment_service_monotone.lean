-- Prove2me | Theorems.Thm_SupplyChainTheory_transshipment_service_monotone
-- name    : SupplyChainTheory.transshipment_service_monotone
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:10:51.163623+00:00
-- url     : https://prove2.me/theorems/fadaa325-4cdb-4b7e-ab62-3a91cf4d8b8f
-- title:
--   Theorem 7.4: with transshipments, the type-1 and type-2 service levels at both retailers are nondecreasing in $S_i$
-- statement:
--   **Theorem 7.4.** In the two-retailer transshipment model with independent demands of finite
--   positive mean, the type-1 and type-2 service levels with transshipments at both $i$ and $j$
--   are nondecreasing in $S_i$: for every fixed $S_j$, each of $\alpha_i(S)$, $\beta_i(S)$,
--   $\alpha_j(S)$ and $\beta_j(S)$ is a monotone function of $S_i$.
--
--   The book omits the proof. Raising $S_i$ shrinks the shortage at $i$ and enlarges the surplus
--   $i$ can send to $j$, and the post-transshipment unmet demand at each retailer is a
--   nonincreasing function of $S_i$ outcome by outcome.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 243, Sect. 7.4.4, Theorem 7.4: 'Proof. Omitted'

import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem transshipment_service_monotone (Sj : ℝ) (Dj Di : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure Dj] [MeasureTheory.IsProbabilityMeasure Di]
    (hj : MeasureTheory.Integrable (fun x => x) Dj)
    (hi : MeasureTheory.Integrable (fun x => x) Di)
    (hposi : 0 < ∫ d, d ∂Di) (hposj : 0 < ∫ d, d ∂Dj) :
    Monotone (fun Si => type1Trans Sj Si Dj Di) ∧ Monotone (fun Si => type2Trans Sj Si Dj Di)
      ∧ Monotone (fun Si => type1Trans Si Sj Di Dj)
      ∧ Monotone (fun Si => type2Trans Si Sj Di Dj) := by sorry

end SupplyChainTheory
