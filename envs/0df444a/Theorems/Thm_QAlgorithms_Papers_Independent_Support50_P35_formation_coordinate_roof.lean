-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_formation_coordinate_roof
-- name    : QAlgorithms.Papers.Independent.Support50.P35.formation_coordinate_roof
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:48:25.442045+00:00
-- url     : https://prove2.me/theorems/5691a6c1-abf1-4872-893f-4343b8c8be5d
-- title:
--   Generalized formation equals the coordinate convex roof
-- statement:
--   Let \(1\leq N\leq M\), let \(f\) be a continuous unitarily invariant concave real function on density matrices on \(\mathbb C^M\), and let \(\rho\) be a normalized bipartite density matrix. Set \(g(\psi)=f(\operatorname{tr}_B|\psi\rangle\langle\psi|)\) for unit vectors. Choose any complete Hermitian orthonormal bipartite operator basis \(\mu\), let \(c(\rho)_\alpha=\operatorname{tr}(\rho\mu_\alpha)\), and let \(V_\mu\) be its normalized pure-projector quadratic variety. Define \(\widetilde g(c)=f(\operatorname{tr}_B\sum_\alpha c_\alpha\mu_\alpha)\). Then
--
--   $$
--   \inf_{\rho=\sum_jp_j|\psi_j\rangle\langle\psi_j|}\sum_jp_jg(\psi_j)
--   =\operatorname{conv}_{V_\mu}\widetilde g\bigl(c(\rho)\bigr).
--   $$
--
--   Both sides range over every positive finite length, nonnegative weights of total one, and normalized components. More precisely, their feasible sets of average costs are equal, and for each normalized finite pure ensemble,
--
--   $$
--   \sum_jp_j|\psi_j\rangle\langle\psi_j|=\rho
--   \iff \sum_jp_jc(|\psi_j\rangle\langle\psi_j|)=c(\rho).
--   $$
--
--   This transfers the actual optimization to affine coordinates. It asserts no additivity or unconditional operational cost interpretation.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 19, Unnumbered p.19: generalized formation is the coordinate convex roof

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.19: generalized formation is exactly a finite coordinate roof;
feasible values and normalized finite barycenters correspond in both directions.
This asserts no unconditional operational interpretation or tensor additivity. -/
theorem formation_coordinate_roof (M N : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (f : Matrix (Fin M) (Fin M) ℂ → ℝ) (hf : IsMarginalCost f)
    (mu : Fin ((M * N) ^ 2) → Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ)
    (hmu : IsHermitianONBasis mu)
    (rho : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) (hrho : IsDensityMatrix rho) :
    formationValues f rho =
      roofValues (generalPureSet mu) (coordinateCost mu f) (hermitianCoordinates mu rho) ∧
    QAlgorithms.Papers.Independent.Information100.P03.convexRoof (fun psi => f (traceRight (pureDensity psi))) rho =
      lowerRoof (generalPureSet mu) (coordinateCost mu f) (hermitianCoordinates mu rho) ∧
    (∀ e : QAlgorithms.Papers.Independent.Information100.P03.PureEnsemble (Fin M × Fin N),
      ensembleDensity e.weight e.vector = rho ↔
        (∑ j, e.weight j • hermitianCoordinates mu (pureDensity (e.vector j))) = hermitianCoordinates mu rho) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
