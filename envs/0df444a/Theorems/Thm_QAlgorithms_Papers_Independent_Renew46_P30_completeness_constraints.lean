-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_completeness_constraints
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.completeness_constraints
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:08:47.599745+00:00
-- url     : https://prove2.me/theorems/fe4c065c-4735-4751-b39d-01bf39c2b1bd
-- title:
--   §IV, Eq.(14): algebraic completeness constraints
-- statement:
--   Use a finite complete orthogonal family of square-integrable irreducible components for a strongly continuous projective unitary representation of a unimodular Lie group. Write $I_{\mu\nu}$ for its coherent intertwiners and $b_\mu>0$ for the coefficient-square Haar integrals. For a positive trace-class seed $\Xi$, weak Haar normalization is equivalent to
--
--   $$\int_GU_g\Xi U_g^\dagger dg=I\quad\Longleftrightarrow\quad\operatorname{Tr}(I_{\mu\nu}\Xi)=\delta_{\mu\nu}b_\mu^{-1}\quad(\mu\sim\nu).$$
--
--   There is no additional constraint on inequivalent pairs. Stabilizer commutation is a separate requirement for descent to the outcome cosets.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 4, §IV, Eq.(14): algebraic completeness constraints

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

/-- PDF p.4, Eq.(14): equivalence of actual normalization and the trace constraints.
The trace uses I_mu_nu, not the reversed I_nu_mu in Eq.(12). -/
theorem completeness_constraints [Fintype M] (hLie : RealLie G) (A : PhysicalOperator H)
    (hA : ContinuousLinearMap.IsPositive A) (hT : IsTraceClass A) :
    WeaklyNormalizedSeed R A ↔ ∀ i j, D.equiv.r i j →
      componentTrace R D i j A = if i = j then ((formalCoefficient R D i)⁻¹ : ℂ) else 0 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
