-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_relativeRenyi_monotone
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.relativeRenyi_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:47:47.579692+00:00
-- url     : https://prove2.me/theorems/bb61c97a-c5f1-4413-bf50-908cb4d0ef3f
-- title:
--   Relative Petz Renyi entanglement is non-entangling monotone
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. A non-entangling map is completely positive and preserves the full separable positive cone. A channel is also trace preserving. Let $\rho$ be any bipartite density matrix, let $\Lambda$ be a non-entangling channel, and let $0\le\alpha\le2$. Define $E_{R,\alpha}$ as the infimum of base-two Petz divergence over all separable density matrices. Then
--
--   $$E_{R,\alpha}(\Lambda(\rho))\le E_{R,\alpha}(\rho).$$
--
--   This includes the mixed-state result and both endpoints.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 10, relative-renyi-monotonicity

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

/-- PDF p.10: Petz relative-Renyi entanglement monotonicity for mixed inputs
and every order in [0,2], including the Umegaki branch. -/
theorem relativeRenyi_monotone {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (alpha : ℝ) (h0 : 0 ≤ alpha) (h2 : alpha ≤ 2)
    (rho : Bip a b) (hrho : IsDensityMatrix rho)
    (L : Superop (Fin a × Fin b) (Fin c × Fin d)) (hL : IsChannel L) (hne : NE L) :
    relativeRenyi alpha (L rho) ≤ relativeRenyi alpha rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
