-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_logarithmic_power_threshold
-- name    : QAlgorithms.Papers.Independent.Support50.P18.logarithmic_power_threshold
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:18:44.139+00:00
-- url     : https://prove2.me/theorems/d0ee2df8-fc14-46f8-ad99-04e3f4e8c19a
-- title:
--   Lemma 2: logarithmic-power spectral threshold
-- statement:
--   Let $q\in\mathbb R$, put $E_k=(\log k)^q$ for $k\ge1$, and retain divergent partition sums as $+\infty$. The value at $k=1$ is fixed to the finite value of the real-power convention; changing this finite prefix does not affect the criterion. Then
--
--   $$\lim_{\lambda\downarrow0}\left(\sum_{k\ge1}e^{-\lambda E_k}\right)^\lambda=1\quad\Longleftrightarrow\quad q>2.$$
--
--   This identifies the spectral threshold for the strengthened Gibbs condition, including its failure at $q=2$.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 8, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P18

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P18

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState traceSize rankOne)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Renew46.P08
  (coefficientEnergy entropySupremum extendedHalfTraceDistance)

/-- Lemma 2, PDF p.8; Appendix proof pp.22--23. Gibbs summability is not assumed. -/
theorem logarithmic_power_threshold (q : ℝ) :
    Tendsto (fun lambda : ℝ => (logPowerPartition q lambda) ^ lambda)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ≥0∞)) ↔ 2 < q := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
