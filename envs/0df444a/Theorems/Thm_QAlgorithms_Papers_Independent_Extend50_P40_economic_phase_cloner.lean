-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_economic_phase_cloner
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.economic_phase_cloner
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:10:24.209356+00:00
-- url     : https://prove2.me/theorems/18c6beb1-b0ab-4b32-9d2f-e86f51e252d8
-- title:
--   §II.D.3 Eqs.(39)–(40): optimal economical phase-covariant cloner
-- statement:
--   For $0\le\theta\le\pi/2$, the economical isometry sends $|0\rangle\mapsto|00\rangle$ and $|1\rangle\mapsto\cos\theta|10\rangle+\sin\theta|01\rangle$. For every equatorial input its fidelities are
--
--   $$
--   F_A=\frac{1+\cos\theta}{2},\qquad F_B=\frac{1+\sin\theta}{2}.
--   $$
--
--   The actual Bloch marginals retain their z biases sin²θ and cos²θ. No phase-independent-fidelity CPTP competitor with first fidelity at least F_A can improve F_B; no ancilla is required.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 12, §II.D.3 Eqs.(39)–(40): optimal economical phase-covariant cloner

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- II.D.3, PDF p.12 Eqs.(39)–(40): economical optimum; z-bias is retained.
The comparison ranges over all phase-covariant-fidelity quantum channels. -/
theorem economic_phase_cloner (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ Real.pi / 2) :
    (economicMatrix theta)ᴴ * economicMatrix theta = 1 ∧
    (∀ a : ℝ, let psi := equator a
      traceRight (pureDensity (economicOutput theta psi)) =
        finBlochDensity ![Real.cos theta * Real.cos a, Real.cos theta * Real.sin a, Real.sin theta ^ 2] ∧
      traceLeft (pureDensity (economicOutput theta psi)) =
        finBlochDensity ![Real.sin theta * Real.cos a, Real.sin theta * Real.sin a, Real.cos theta ^ 2] ∧
      pureFidelity psi (traceRight (pureDensity (economicOutput theta psi))) = (1 + Real.cos theta) / 2 ∧
      pureFidelity psi (traceLeft (pureDensity (economicOutput theta psi))) = (1 + Real.sin theta) / 2) ∧
    (∀ (T : Superop (Fin 2) (Fin 2 × Fin 2)) (fA fB : ℝ), IsChannel T →
      (∀ a : ℝ, pureFidelity (equator a) (traceRight (T (pureDensity (equator a)))) = fA ∧
        pureFidelity (equator a) (traceLeft (T (pureDensity (equator a)))) = fB) →
      (1 + Real.cos theta) / 2 ≤ fA → fB ≤ (1 + Real.sin theta) / 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
