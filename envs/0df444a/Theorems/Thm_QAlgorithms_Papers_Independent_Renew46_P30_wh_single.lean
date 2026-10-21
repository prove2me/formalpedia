-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_wh_single
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.wh_single
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:15:19.908746+00:00
-- url     : https://prove2.me/theorems/66ba1bbf-a6d5-4cee-ac58-ce54e0f0d701
-- title:
--   §V.B.1: single-mode displacement optimum
-- statement:
--   Use the completed oscillator Fock space $\ell^2(\mathbb N)$, the bounded displacement selected by the actual number coefficients of $D(z)=\exp(za^\dagger-\overline z a)$, and the reference measure $d^2z/\pi$. The selected displacement realizes these coefficients and is unitary. For every unit input $\psi$, the coefficient-square integral and the optimum satisfy
--
--   $$\int_{\mathbb C}|\langle\psi,D(z)\psi\rangle|^2\frac{d^2z}{\pi}=1,\qquad\Xi=|\psi\rangle\langle\psi|,\qquad L_{\max}=1.$$
--
--   The positive seed integrates weakly to the identity and defines a normalized bounded operator measure. The bound also holds for regular positive-form covariant seeds whose invariant domain contains the input. For vacuum input the translated seed is the coherent-state heterodyne POVM. No photon cutoff or arbitrary Weyl family is assumed.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 6, §V.B.1: single-mode displacement optimum

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

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet displacement displacementMatrix coherentMeasure coherentKet)

/-- PDF p.6, §V.B.1: bounded Weyl realization, formal coefficient 1,
normalized rank-one optimum for every unit full-Fock input, and vacuum heterodyne identity. -/
theorem wh_single :
    QAlgorithms.Papers.Independent.Dependency50.P39.DisplacementRealized ∧
    (∀ psi : Fock, ‖psi‖ = 1 →
      Integrable (fun z => ‖inner ℂ psi (displacement z psi)‖ ^ 2) coherentMeasure ∧
      (∫ z, ‖inner ℂ psi (displacement z psi)‖ ^ 2 ∂coherentMeasure) = 1 ∧
      ContinuousLinearMap.IsPositive (InnerProductSpace.rankOne ℂ psi psi) ∧
      FockNormalized (InnerProductSpace.rankOne ℂ psi psi) ∧
      BoundedPOVM coherentMeasure (fockOrbit (InnerProductSpace.rankOne ℂ psi psi)) ∧
      pureSeedDensity (InnerProductSpace.rankOne ℂ psi psi) psi = 1 ∧
      (∀ A : FockOperator, ContinuousLinearMap.IsPositive A → FockNormalized A → pureSeedDensity A psi ≤ 1) ∧
      (∀ A : FormSeed coherentMeasure (fun z : ℂ => ContinuousLinearMap.adjoint (displacement z)),
        psi ∈ A.domain → (A.form psi psi).re ≤ 1)) ∧
    (∀ z : ℂ, displacement z (fockKet 0) = coherentKet z ∧
      fockOrbit (InnerProductSpace.rankOne ℂ (fockKet 0) (fockKet 0)) z =
        InnerProductSpace.rankOne ℂ (coherentKet z) (coherentKet z)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
