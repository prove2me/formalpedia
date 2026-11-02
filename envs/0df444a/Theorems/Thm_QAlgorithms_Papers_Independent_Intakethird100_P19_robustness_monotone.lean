-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_robustness_monotone
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.robustness_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:47:07.259203+00:00
-- url     : https://prove2.me/theorems/152a6f79-07ae-459f-a6b3-b477c45dc200
-- title:
--   Standard robustness is non-entangling monotone
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. A non-entangling map is completely positive and preserves the full separable positive cone. A channel is also trace preserving. For every bipartite state $\rho$ and non-entangling channel $\Lambda$ between arbitrary positive local dimensions,
--
--   $$R(\Lambda(\rho))\le R(\rho).$$
--
--   Here $R$ is standard robustness, using separable normalized noise.
--
--   This extends the robustness comparison to arbitrary mixed states.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 8, robustness-monotonicity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- PDF p.8, paragraph preceding Theorem 1: standard robustness monotonicity
under non-entangling channels on arbitrary mixed states. -/
theorem robustness_monotone {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (rho : Bip a b) (hrho : IsDensityMatrix rho)
    (L : Superop (Fin a × Fin b) (Fin c × Fin d)) (hL : IsChannel L) (hne : NE L) :
    standardStateRobustness (L rho) ≤ standardStateRobustness rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
