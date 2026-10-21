-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_renyi_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P23.renyi_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:56:02.468993+00:00
-- url     : https://prove2.me/theorems/d876b9b1-d41d-466e-b4f1-234d3a03aa83
-- title:
--   Proposition 2.11
-- statement:
--   Let $\rho,\nu$ be nonorthogonal normalized states on a nonzero finite-dimensional complex Hilbert space. Their support-restricted Rényi log-overlap $S_\alpha(\rho\mid\nu)$ is defined for every real $\alpha$. Then $$S_0(\rho\mid\nu)=\log\nu(s(\rho)),\quad S_1(\rho\mid\nu)=\log\rho(s(\nu)),\quad S_\alpha(\rho\mid\nu)=S_{1-\alpha}(\nu\mid\rho).$$ It is convex in $\alpha$ and invariant under simultaneous unitary conjugation. When the supports are equal it is strictly convex exactly when $\rho\ne\nu$.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 45, Proposition 2.11

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Proposition2.11, all five clauses, source PDF p.45; equal supports only in clause4. -/
theorem renyi_properties [Nonempty I] (rho nu : Mat I) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hnu : QAlgorithms.IsDensityMatrix nu) (hnorth : ¬Orthogonal rho nu) :
    renyi rho nu 0 = ENNReal.log (ENNReal.ofReal (ev nu (support rho))) ∧
    renyi rho nu 1 = ENNReal.log (ENNReal.ofReal (ev rho (support nu))) ∧
    ConvexOn ℝ Set.univ (renyiReal rho nu) ∧
    (∀ U : Matrix.unitaryGroup I ℂ, ∀ a : ℝ,
      renyi ((U : Mat I) * rho * (U : Mat I)ᴴ)
        ((U : Mat I) * nu * (U : Mat I)ᴴ) a = renyi rho nu a) ∧
    (support rho = support nu → (StrictConvexOn ℝ Set.univ (renyiReal rho nu) ↔ rho ≠ nu)) ∧
    (∀ a : ℝ, renyi rho nu a = renyi nu rho (1-a)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
