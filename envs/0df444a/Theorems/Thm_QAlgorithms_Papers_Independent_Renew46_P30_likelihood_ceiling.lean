-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_likelihood_ceiling
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.likelihood_ceiling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:10:11.53962+00:00
-- url     : https://prove2.me/theorems/1e1a7ef4-75d6-4cd9-bc02-6aa9187a2846
-- title:
--   §IV, Eq.(15): pure-input likelihood ceiling
-- statement:
--   Let a strongly continuous projective unitary representation of a unimodular Lie group on a complete complex Hilbert space have a countable complete orthogonal decomposition into square-integrable irreducible components. Let $P_\mu$ be the component projections, $b_\mu$ the Haar coefficient integrals, $\psi$ a unit input with compact ray stabilizer, and $\Xi$ any normalized positive bounded covariant seed. Set $c_\mu=\|P_\mu\psi\|$ and $M_\psi=\{\mu:c_\mu>0\}$. Then
--
--   $$\langle\psi,\Xi\psi\rangle\le\left(\sum_\mu c_\mu\sqrt{b_\mu^{-1}}\right)^2\le\sum_{\mu\in M_\psi}b_\mu^{-1}.$$
--
--   The nonnegative sums and inequalities are interpreted in $[0,\infty]$. This is an upper bound; it does not assert that the coarser last expression is attained for a fixed input.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 4, §IV, Eq.(15): pure-input likelihood ceiling

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P30

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39 (IsTraceClass)

open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)

open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)

open scoped ComplexConjugate ComplexOrder Manifold ContDiff ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (R : CovariantHilbertData G H)

variable {M : Type*} [DecidableEq M]

variable (D : Components R M)

/-- PDF p.4, Eq.(15): countable-component sharp and coarse ceilings.
No infinite eta is asserted to be a Hilbert vector. -/
theorem likelihood_ceiling [Countable M] (hLie : RealLie G) (psi : H)
    (hn : ‖psi‖ = 1) (K : Subgroup G) (hK : RayStabilizer R psi K)
    (A : PhysicalOperator H) (hA : Seed R K A) :
    ENNReal.ofReal (pureSeedDensity A psi) ≤ sharpBound R D psi ∧
      sharpBound R D psi ≤ coarseBound R D psi := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
