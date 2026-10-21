-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_finite_twirling
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.finite_twirling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:04:15.209896+00:00
-- url     : https://prove2.me/theorems/e57854df-9c13-4140-b6be-2b9cbafa962b
-- title:
--   §III, Eq.(12): finite-component weak twirling formula
-- statement:
--   Let a strongly continuous projective unitary representation of a unimodular Lie group $G$ act on a complete complex Hilbert space $\mathcal H$. Fix its two-sided Haar measure $dg$, normalized to mass one when $G$ is compact, and a finite complete orthogonal decomposition into nonzero square-integrable irreducible components $\mathcal H_\mu$. Let $I_{\mu\nu}$ be coherent partial unitary intertwiners on equivalent pairs, extended by zero elsewhere. For a unit vector $e_\mu\in\mathcal H_\mu$, put $b_\mu=\int_G|\langle e_\mu,U_g e_\mu\rangle|^2dg$. These numbers are positive, independent of the chosen unit vector, and equal on equivalent components. For every trace-class operator $O$, all matrix coefficients of its twirl are integrable and
--
--   $$\int_G U_g O U_g^\dagger dg=\sum_\mu\sum_{\nu\sim\mu}b_\mu\operatorname{Tr}(I_{\nu\mu}O)I_{\mu\nu}.$$
--
--   The integral is weak; the component Hilbert spaces can be infinite dimensional. This formula converts Haar normalization into algebraic trace constraints.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 3, §III, Eq.(12): finite-component weak twirling formula

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

/-- PDF p.3, Eq.(12): finite-component trace-class weak twirling, with actual
integrability, positive b_mu, and independence of the chosen unit vector. -/
theorem finite_twirling [Fintype M] (hLie : RealLie G) (A : PhysicalOperator H) (hA : IsTraceClass A) :
    (∀ i, 0 < formalCoefficient R D i) ∧
    (∀ i j, D.equiv.r i j → formalCoefficient R D i = formalCoefficient R D j) ∧
    (∀ i v, D.I i i v = v → ‖v‖ = 1 →
      (∫ g, ‖inner ℂ v (R.U g v)‖ ^ 2 ∂(R.dg)) = formalCoefficient R D i) ∧
    WeakIntegral R.dg (conjugatedSeed R A)
      (∑ i, ∑ j, if D.equiv.r i j then
        ((formalCoefficient R D i : ℂ) * componentTrace R D j i A) • D.I i j else 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
