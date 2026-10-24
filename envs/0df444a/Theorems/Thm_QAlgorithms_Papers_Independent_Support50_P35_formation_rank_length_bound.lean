-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_formation_rank_length_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P35.formation_rank_length_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:49:08.684654+00:00
-- url     : https://prove2.me/theorems/c20523d9-d1ce-4439-8c70-47284fff4b93
-- title:
--   Corrected rank-dependent length restriction for formation
-- statement:
--   Let \(1\leq N\leq M\), let \(f\) be continuous, unitarily invariant, and concave on density matrices on \(\mathbb C^M\), and let \(\rho\) be a normalized density matrix on \(\mathbb C^M\otimes\mathbb C^N\). Put \(r=\operatorname{rank}\rho\). Then
--
--   $$
--   \inf_{\rho=\sum_jp_j|\psi_j\rangle\langle\psi_j|}\sum_jp_jf(\operatorname{tr}_B|\psi_j\rangle\langle\psi_j|)
--   =
--   \inf_{\substack{r\leq s\leq r^2\\\rho=\sum_{j=1}^sp_j|\psi_j\rangle\langle\psi_j|}}
--   \sum_{j=1}^sp_jf(\operatorname{tr}_B|\psi_j\rangle\langle\psi_j|).
--   $$
--
--   Every decomposition is finite and normalized, with unit vectors and nonnegative weights of total one. The left side allows every finite length. The printed \(r\geq s\geq r^2\) is corrected using the explicit \(s\geq r\) discussion on p.17 and the intended finite upper bound. For rank one the restricted interval is exactly \(s=1\). This restriction preserves the optimization value rather than using an empty-set default.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 19, Eq.(61): corrected rank-dependent decomposition-length restriction

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF pp.17,19, Eq.(61), corrected r<=s<=r^2: restricting the finite
formation infimum to this rank-dependent interval leaves its value unchanged. -/
theorem formation_rank_length_bound (M N : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (f : Matrix (Fin M) (Fin M) ℂ → ℝ) (hf : IsMarginalCost f)
    (rho : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) (hrho : IsDensityMatrix rho) :
    QAlgorithms.Papers.Independent.Information100.P03.convexRoof (fun psi => f (traceRight (pureDensity psi))) rho =
      sInf (rankRestrictedValues f rho) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
