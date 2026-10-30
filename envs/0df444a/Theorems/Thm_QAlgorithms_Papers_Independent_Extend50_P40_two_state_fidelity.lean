-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_two_state_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.two_state_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:08:54.415576+00:00
-- url     : https://prove2.me/theorems/529307d2-75a3-4673-a332-8cd62883a464
-- title:
--   §II.D.1 Eq.(34): symmetric cloning of two pure qubit states
-- statement:
--   Let $\psi_0,\psi_1$ be normalized qubit states, $s=|\langle\psi_0|\psi_1\rangle|$, and $q=\sqrt{1-2s+9s^2}$. The optimum common fidelity on both inputs and both output sites is $F(0)=1$ and, for $s>0$,
--
--   $$
--   F(s)=\frac12+\frac{\sqrt2}{32s}(1+s)(3-3s+q)\sqrt{-1+2s+3s^2+(1-s)q}.
--   $$
--
--   A fixed CPTP channel attains this value and every channel with a common fidelity is bounded by it. Also F(1)=1 and F(1/2) is a minimum on [0,1]; the rounded decimal is not asserted as an equality.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 11, §II.D.1 Eq.(34): symmetric cloning of two pure qubit states

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

/-- II.D.1, PDF p.11 Eq.(34): exact common symmetric two-state fidelity, including
s=0 and s=1 endpoints and its exact minimizing pureFidelity s=1/2. -/
theorem two_state_fidelity (psi0 psi1 : EuclideanSpace ℂ (Fin 2)) (h0 : ‖psi0‖ = 1) (h1 : ‖psi1‖ = 1) :
    let s := ‖inner ℂ psi0 psi1‖
    (∃ T : Superop (Fin 2) (Fin 2 × Fin 2), IsChannel T ∧
      ∀ psi ∈ ({psi0, psi1} : Set (EuclideanSpace ℂ (Fin 2))),
        pureFidelity psi (traceRight (T (pureDensity psi))) = twoStateFidelity s ∧
        pureFidelity psi (traceLeft (T (pureDensity psi))) = twoStateFidelity s) ∧
    (∀ (T : Superop (Fin 2) (Fin 2 × Fin 2)) (f : ℝ), IsChannel T →
      (∀ psi ∈ ({psi0, psi1} : Set (EuclideanSpace ℂ (Fin 2))),
        pureFidelity psi (traceRight (T (pureDensity psi))) = f ∧
        pureFidelity psi (traceLeft (T (pureDensity psi))) = f) → f ≤ twoStateFidelity s) ∧
    twoStateFidelity 0 = 1 ∧ twoStateFidelity 1 = 1 ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, twoStateFidelity (1 / 2) ≤ twoStateFidelity t) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
